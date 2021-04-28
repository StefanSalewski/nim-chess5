# basic chess engine in Nim
# v 0.5 2021-FEB-07
# c S. Salewski
#
# TODO: make transposition table size configurable?
# TODO: make aggression configurable
# TODO: make aggression depending on winning/loosing
# TODO: use xxhash
# TODO: add optional random noise

from sequtils import keepIf, anyIt
from times import cpuTime
import sets
import hashes

var ENDG = false

proc print

# fast abs() for not too large integers -- not used, seems to give no performance increase
template xbs(i: int): int =
  assert(i > low(int) div 2)
  i - (i < 0).int * i * 2

template countupImpl2(incr: untyped) {.dirty.} =
  #when T is IntLikeForCount:
  #  var res = int(a)
  #  while true:
  #    yield T(res)
  #    incr
  #else:
  var res = a
  while true:
    yield res
    incr

iterator countupBy[T](a: T; step = 1): T {.inline.} =
  ## Counts from ordinal value `a` up with the given
  ## step size. `T` may be any ordinal type, `step` may
  ## be positive or negative.
  countupImpl2:
    inc(res, step)

iterator countup[T](a: T): T {.inline.} =
  ## Counts from ordinal value `a` up with
  ## step size 1. `T` may be any ordinal type.
  countupImpl2:
    inc(res, 1)

iterator `>=`[T](a: T): T {.inline.} =
  ## An alias for `countup`.
  countupImpl2:
    inc(res, 1)

proc `:=`(x: var int; v: int): int {.inline, noinit.} =
  x = v
  result = v

type BitBuffer192 = tuple
  data: array[24, int8]
  #pos: int

#[
proc writeToBitBuffer(b: var BitBuffer192; n: int8; d: int8) {.inline.} =
  if d != 0:
    var buffer: int16 = d.int16
    let byteIndex = b.pos div 8
    let bitIndex = b.pos mod 8
    buffer = buffer shl bitIndex
    b.data[byteIndex] = b.data[byteIndex] or cast[int8](buffer)
    buffer = buffer shr 8
    #if buffer != 0:
    b.data[byteIndex + 1] = b.data[byteIndex + 1] or cast[int8](buffer)
  b.pos += n
]#

const
  StalemateMarker* = high(int)
  StopGameMarker* = high(int) - 1

const
  MaxDepth = 15
  MaxMob = 64

const
  VoidID = 0
  PawnID = 1
  KnightID = 2
  BishopID = 3
  RookID = 4
  QueenID = 5
  KingID = 6
  WPawn = PawnID
  WKnight = KnightID
  WBishop = BishopID
  WRook = RookID
  WQueen = QueenID
  WKing = KingID
  BPawn = -PawnID
  BKnight = -KnightID
  BBishop = -BishopID
  BRook = -RookID
  BQueen = -QueenID
  BKing = -KingID

const
  Forward = 8
  Sideward = 1
  S = Forward
  O = Sideward
  N = -S
  W = -O
  NO = N + O
  SO = S + O
  NW = N + W
  SW = S + W

  PawnDirsWhite = [Forward - Sideward, Forward + Sideward, Forward, Forward + Forward]
  BishopDirs = [NO, SO, NW, SW]
  RookDirs = [N, O, S, W]
  KnightDirs = [N + NO, N + NW, W + NW, W + SW, O + NO, O + SO, S + SO, S + SW]
  KingDirs = [N, O, S, W, NO, SO, NW, SW] # KingDirs = BishopDirs + RookDirs

  #Agility = [0, 4, 6, 5, 3, 2, 1] # Pawn .. King, how often is that piece used in smart average game play.

const                              # we try to keep all the values small to fit in two bytes
  AB_Inf = 32000                   # more than the summed value of all pieces
  VoidValue = 0
  PawnValue = 100
  KnightValue = 300
  BishopValue = 300
  RookValue = 500
  QueenValue = 900
  KingValue = 18000                # more than the summed value of all other pieces
  SureCheckmate* = KingValue div 2 #  still more than the summed value of all other pieces, but less than value of a king

  FigureValue: array[0..KingID, int] = [VoidValue, PawnValue, KnightValue, BishopValue, RookValue, QueenValue, KingValue]
  FigureVax: array[0..KingID, int] = [VoidValue, PawnValue, KnightValue - 1, BishopValue, RookValue, QueenValue, KingValue]
  # try Knight before Bishop

const
  Setup = [
    WRook, WKnight, WBishop, WKing, WQueen, WBishop, WKnight, WRook,
    WPawn, WPawn, WPawn, WPawn, WPawn, WPawn, WPawn, WPawn,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    BPawn, BPawn, BPawn, BPawn, BPawn, BPawn, BPawn, BPawn,
    BRook, BKnight, BBishop, BKing, BQueen, BBishop, BKnight, BRook]

# the traditional row and column designators -- B prefix for Board
const BA = 7
const BB = 6
const BC = 5
const BD = 4
const BE = 3
const BF = 2
const BG = 1
const BH = 0
const B1 = 0
const B2 = 1
const B3 = 2
const B4 = 3
const B5 = 4
const B6 = 5
const B7 = 6
const B8 = 7

const PosRange = 0..63

type
  Color = enum Black = -1, White = 1
  ColorIndex = 0 .. 1
  Position = 0 .. 63
  Col = 0 .. 7
  Row = 0 .. 7
  FigureID = int
  Board* = array[Position, FigureID]
  BoardControl = array[-64 .. 64, int]
  HasMoved = array[Position, bool]
  Mobset = array[Position, set[0 .. MaxDepth]]
  PawnPressure = array[Position, set[0 .. MaxDepth]]
  Freedom = array[-KingID .. KingID, array[Position, int]] # VoidID..KingID; Maybe we should call it happyness

type
  Gnu = tuple # move precalculation is based on old gnuchess ideas...
    pos: int
    nxtDirIdx: int

  Path = array[Position, array[Position, Gnu]]

const
  InvalidScore = low(int16)

type
  Guide = tuple
    v: int16
    si: int8
    di: int8

  HashLine = array[0..MaxDepth, Guide]

  HashResult = tuple
    score: HashLine # exact values
    floor: HashLine # lower bounds
    pri: int

  TTE = tuple
    res: HashResult
    key: array[24, int8]

  TT = seq[TTE]

var tt = newSeq[TTE](1024 * 1024 * 2)
var history = initHashSet[array[24, int8]]()

const
  TTTry = 7

proc getTTE(key: array[24, int8]; res: var HashResult): int {.inline.} =
  #let h0 = xxh64int824(key, 45235497)
  let h0 = key.hash
  for i in 0 .. TTTry:
    let h = (h0 + i) and tt.high
    if tt[h].key == key:
      res = tt[h].res
      return h
  return -1

var
  iscol, nocol: int

proc putTTE(key: array[24, int8]; res: var HashResult; pri: int) {.inline.} =
  #let h0 = xxh64int824(key, 45235497)
  let h0 = key.hash
  for i in 0 .. TTTry:
    let h = (h0 + i) and tt.high
    if tt[h].res.pri < pri:
      res.pri = pri
      tt[h].res = res
      tt[h].key = key
      inc(nocol)
      return
  inc(iscol)

proc genHashResultAllZeroConst: HashLine {.inline.} =
  #for i in mitems(result): i.v = InvalidScore # compiler bug #4741
  for i in result.low .. result.high:
    result[i].v = InvalidScore

const
  HashResultAllZero = genHashResultAllZeroConst()

proc initHR(hr: var HashResult) {.inline.} =
  hr.score = HashResultAllZero
  hr.floor = HashResultAllZero

var # we use global data for now
  board: Board
  boardControl: BoardControl
  mobSet: Mobset
  hasMoved: HasMoved
  pawnPressure: PawnPressure
  freedom: Freedom
  pawnPath: array[ColorIndex, Path]
  knightPath: Path
  bishopPath: Path
  rookPath: Path
  kingPath: Path
  pjm = -1

# proc sameSign(i: int; j: Color): bool = (i.int xor j.int) >= 0

template umod8(i: typed): untyped = i and 7

template udiv8(i: typed): untyped = i shr 3

proc sign(x: int): int {.inline.} =
  (x > 0).int - (x < 0).int

proc even(i: int): bool {.inline.} = (i and 1) == 0

proc odd(i: int): bool {.inline.} = (i and 1) != 0

proc sqr(i: int): int {.inline.} = i * i

proc clear[T](s: var seq[T]) {.inline.} = s.setLen(0)

proc isVoid(p: Position): bool {.inline.} = board[p] == VoidID

proc isAPawn(p: Position): bool {.inline.} = board[p].sqr == PawnID # = board[p].abs == PawnID

proc isAKing(p: Position): bool {.inline.} = board[p].sqr == KingID * KingID

proc colIdx(c: Color): ColorIndex {.inline.} = (c.int + 1) shr 1 # div 2

proc isWhite(c: Color): bool {.inline.} = c == White

proc isBlack(c: Color): bool {.inline.} = c == Black

proc oppColor(c: Color): Color {.inline.} = (-c.int).Color

proc col(p: Position): Col {.inline.} = umod8(p) # p mod 8

proc row(p: Position): Row {.inline.} = udiv8(p) # p div 8

proc baseRow(p: Position): bool {.inline.} = row(p) == 0 or row(p) == 7 # (p div 8) mod 7 == 0

proc row2or5(p: Position): bool {.inline.} = row(p) == 2 or row(p) == 5 # (row(p) - 2) mod 3 == 0

proc rowsToGo(p: Position; c: Color): int {.inline.} =
  if c == Black: row(p) else: 7 - row(p)

proc fasterWriteToBitBuffer(): BitBuffer192 =
  const
    L: array[-KingID .. KingID, int8] = [6.int8, 6, 6, 6, 6, 3, 1, 3, 6, 6, 6, 6, 6]
    Code: array[-KingID .. KingID, int8] = [0b111000.int8, 0b111001, 0b110000, 0b110001, 0b110010, 0b100, 0b0, 0b101, 0b110011,
        0b110100, 0b110101, 0b111010, 0b111011]
  var buf: int64
  var shift = 0
  var bpos = 0
  for f in board:
    let newbits: int64 = Code[f]
    buf = buf or (newbits shl shift)
    shift += L[f]
    if unlikely(shift >= 8 * 8):
      cast[var int64](addr(result.data[bpos])) = buf
      bpos += 8
      shift -= 8 * 8
      buf = newbits shr (L[f] - shift)
  cast[var int64](unsafeaddr(result.data[bpos])) = buf


proc nomuchFasterWriteToBitBuffer(): BitBuffer192 =
  const
    L: array[-KingID .. KingID, int8] = [6.int8, 6, 6, 6, 6, 3, 1, 3, 6, 6, 6, 6, 6]
    Code: array[-KingID .. KingID, int8] = [0b111000.int8, 0b111001, 0b110000, 0b110001, 0b110010, 0b100, 0b0, 0b101, 0b110011,
        0b110100, 0b110101, 0b111010, 0b111011]
  var buf: int64
  var shift = 0
  var bpos = 0
  for i in 0 .. 7:
    for j in 0 .. 7:
      let f = board[i * 8 + j]
      let newbits: int64 = Code[f]
      buf = buf or (newbits shl shift)
      shift += L[f]
    cast[var int64](addr(result.data[bpos])) = buf
    bpos += shift div 8
    buf = buf shr ((shift div 8) * 8)
    shift -= (shift div 8) * 8
    #buf = buf shr shift


proc xmuchFasterWriteToBitBuffer(): BitBuffer192 =
  const
    L: array[-KingID .. KingID, int8] = [6.int8, 6, 6, 6, 6, 3, 1, 3, 6, 6, 6, 6, 6]
    Code: array[-KingID .. KingID, int8] = [0b111000.int8, 0b111001, 0b110000, 0b110001, 0b110010, 0b100, 0b0, 0b101, 0b110011,
        0b110100, 0b110101, 0b111010, 0b111011]
  var buf: int64
  var shift = 0
  var bpos = 0
  for i in 0 .. 7:
    for j in 0 .. 7:
      let f = board[i * 8 + j]
      #let newbits: int64 = Code[f]
      buf = buf or (Code[f] shl shift)
      shift += L[f]
    cast[var int64](addr(result.data[bpos])) = buf
    bpos += shift shr 3 # div 8
    #let r = shift and (not 7)
    let r = ((shift div 8) * 8)
    buf = buf shr r # ((shift div 8) * 8)
    shift -= r # (shift div 8) * 8
    #buf = buf shr shift

proc xxxmuchFasterWriteToBitBuffer(): BitBuffer192 =
  const
    L: array[-KingID .. KingID, int8] = [6.int8, 6, 5, 5, 5, 3, 1, 3, 5, 5, 5, 6, 6]
    Code: array[-KingID .. KingID, int8] = [0b111100.int8, 0b111101, 0b11000, 0b11001, 0b11010,  0b100, 0b0, 0b101, 0b11011, 0b11100, 0b11101, 0b111110, 0b111111]
  var buf: int64
  var shift = 0
  var bpos = 0
  var bp = 0
  for i in 0 .. 7:
    for j in 0 .. 7:
      #let f = board[i * 8 + j]
      let f = board[bp]; inc(bp)
      let newbits: int64 = Code[f]
      buf = buf or (newbits shl shift)
      shift += L[f]
    cast[var int64](addr(result.data[bpos])) = buf
    echo shift, " ", bpos


    assert bpos + 8 <= 24
    bpos += shift shr 3 # div 8
    #let r = ((shift div 8) * 8)
    let r = shift and (not 7)
    buf = buf shr r
    shift -= r
    #buf = buf shr shift


proc yyymuchFasterWriteToBitBuffer(): BitBuffer192 =
  const
    L: array[-KingID .. KingID, int8] = [6.int8, 6, 5, 5, 5, 3, 1, 3, 5, 5, 5, 6, 6]
    Code: array[-KingID .. KingID, int8] = [0b111100.int8, 0b111101, 0b11000, 0b11001, 0b11010,  0b100, 0b0, 0b101, 0b11011, 0b11100, 0b11101, 0b111110, 0b111111]
  var buf: int64
  var shift = 0
  var bpos = 0
  var bp = 0
  for i in 0 .. 3:
    #bp = i * 16
    bp = i
    for j in 0 .. 7:
      #let f = board[i * 8 + j]
      let f = board[bp]; inc(bp, 8)
      let newbits: int64 = Code[f]
      buf = buf or (newbits shl shift)
      shift += L[f]

    bp = i + 4
    for j in 0 .. 7:
      #let f = board[i * 8 + j]
      let f = board[bp]; inc(bp, 8)
      let newbits: int64 = Code[f]
      buf = buf or (newbits shl shift)
      shift += L[f]

    cast[var int64](addr(result.data[bpos])) = buf
    echo shift, " ", bpos


    assert bpos + 8 <= 24
    bpos += shift shr 3 # div 8
    #let r = ((shift div 8) * 8)
    let r = shift and (not 7)
    buf = buf shr r
    shift -= r
    #buf = buf shr shift






proc muchFasterWriteToBitBuffer(): BitBuffer192 =
  const
    L: array[-KingID .. KingID, int8] = [6.int8, 6, 5, 5, 5, 3, 1, 3, 5, 5, 5, 6, 6]
    Code: array[-KingID .. KingID, int8] = [0b111100.int8, 0b111101, 0b11000, 0b11001, 0b11010,  0b100, 0b0, 0b101, 0b11011, 0b11100, 0b11101, 0b111110, 0b111111]
  var collector: array[4 * 8, int8]
  var buf: int64
  var shift = 0
  var bpos = 0
  var bp = 0
  for i in 0 .. 3:
    #bp = i * 16
    bp = i
    for j in 0 .. 7:
      #let f = board[i * 8 + j]
      let f = board[bp]; inc(bp, 8)
      let newbits: int64 = Code[f]
      buf = buf or (newbits shl shift)
      shift += L[f]

    #bp = i + 4 * 8
    bp = i + 4
    for j in 0 .. 7:
      #let f = board[i * 8 + j]
      let f = board[bp]; inc(bp, 8)
      let newbits: int64 = Code[f]
      buf = buf or (newbits shl shift)
      shift += L[f]

    cast[var int64](addr(collector[bpos])) = buf
    #echo shift, " ", bpos


    assert bpos + 8 <= 32
    bpos += shift shr 3 # div 8
    #let r = ((shift div 8) * 8)
    let r = shift and (not 7)
    buf = buf shr r
    shift -= r
    #buf = buf shr shift


  result.data = cast[ptr typeof(result.data)](addr collector)[]

  #echo collector
  #echo result.data  






proc encodeBoard(c: Color; depthleft: int): BitBuffer192 {.inline.} =
  var i = 0 # [16 .. 23, 40 .. 47]
  if depthleft >= 0:
    i = 16
    while i < 48:
      if i == 23: i = 40
      # i += (i == 23).int * 17
      if depthleft in mobSet[i]:
        break
      inc i
    if i == 48: i = 0 # pawn jump position -- if != 0 then there was a pawn jump just before
    # i = i mod 48
  #for i, f in board:
  #  writeToBitBuffer(result, L[f], Code[f])
  #let hhh = evenFasterwriteToBitBuffer()
  #echo repr(result.data)
  #echo repr(hhh.data)
  result = muchFasterWriteToBitBuffer()
  #assert result == fasterWriteToBitBuffer()
  #assert result.data == hhh.data
  result.data[22] = cast[int8](hasMoved[0].ord or hasMoved[3].ord * 2 or hasMoved[7].ord * 4 or hasMoved[56].ord * 8 or hasMoved[
      59].ord * 16 or hasMoved[63].ord * 32)
  result.data[23] = cast[int8](i or (c.int + 1) div 2 * 64)
  #echo "-"
  #echo fasterWriteToBitBuffer()
  #echo muchFasterWriteToBitBuffer()
  #assert muchFasterWriteToBitBuffer() == fasterWriteToBitBuffer()

proc offBoard64(dst: int): bool {.inline.} = dst < Board.low or dst > Board.high

# do we not cross the border of the board when figure is moved in a regular way
proc moveIsValid(src: Position; dst: int): bool {.inline.} =
  not offBoard64(dst) and (col(src) - col(dst)).abs <= 1

proc knightMoveIsValid(src: Position; dst: int): bool {.inline.} =
  not offBoard64(dst) and (col(src) - col(dst)).abs <= 2

proc pawnMoveIsValid(c: Color; src, dst: int): bool {.inline.} =
  result = moveIsValid(src, dst)
  if result and (src - dst).abs == 16:
    result = if c.isWhite: row(src) == B2 else: row(src) == B7

proc initRook {.inline.} =
  for src in PosRange:
    var i = 0
    for d in RookDirs:
      var pos = src
      while true:
        var dst = pos + d
        if not moveIsValid(pos, dst): break
        rookPath[src][i].pos = if pos == src: -dst else: dst # mark start pos for this dir
        inc i
        pos = dst
    var nxtDirStart = i # index of the last terminal node
    rookPath[src][i].pos = -1 # terminator
    while i > 0:
      dec i
      rookPath[src][i].nxtDirIdx = nxtDirStart
      if rookPath[src][i].pos < 0:
        nxtDirStart = i
        rookPath[src][i].pos *= -1

proc initBishop {.inline.} =
  for src in PosRange:
    var i = 0
    for d in BishopDirs:
      var pos = src
      while true:
        var dst = pos + d
        if not moveIsValid(pos, dst): break
        bishopPath[src][i].pos = if pos == src: -dst else: dst
        inc i
        pos = dst
    var nxtDirStart = i
    bishopPath[src][i].pos = -1
    freedom[WBishop][src] = (i - 10) * 4 # range -12..12 # abs val is big enough, so exchange of a
    freedom[WQueen][src] = (i - 10) * 4 # range -12..12 # pawn for very good position may occur
    freedom[BBishop][src] = (i - 10) * 4
    freedom[BQueen][src] = (i - 10) * 4
    while i > 0:
      dec i
      bishopPath[src][i].nxtDirIdx = nxtDirStart
      if bishopPath[src][i].pos < 0:
        nxtDirStart = i
        bishopPath[src][i].pos *= -1

proc initKnight {.inline.} =
  for src in PosRange:
    var i = 0
    for d in KnightDirs:
      if knightMoveIsValid(src, src + d):
        knightPath[src][i].pos = src + d
        knightPath[src][i].nxtDirIdx = i + 1 # not really needed
        inc i
    knightPath[src][i].pos = -1
    freedom[WKnight][src] = (i - 5) * 4 # range -12..12
    freedom[BKnight][src] = (i - 5) * 4

proc initKing {.inline.} =
  for src in PosRange:
    var i = 0
    for d in KingDirs:
      if moveIsValid(src, src + d):
        kingPath[src][i].pos = src + d
        kingPath[src][i].nxtDirIdx = i + 1
        inc i
    kingPath[src][i].pos = -1
    if src == 0 or src == 7 or src == 56 or src == 63:
      freedom[WKing][src] = -16
      freedom[BKing][src] = -16

# the first two moves are possible captures or -1 if at the border of the board
proc initPawn(color: Color) =
  for src in PosRange:
    var i = 0
    for d in PawnDirsWhite:
      pawnPath[color.colIdx][src][i].pos =
        if pawnMoveIsValid(color, src, src + d * color.int): src + d * color.int else: -1
      pawnPath[color.colIdx][src][i].nxtDirIdx = i + 1 # not really needed
      inc i
    pawnPath[color.colIdx][src][i].pos = -1

type
  KK = tuple # source figure, destination figure, source index, destination index and score
    sf: int
    df: int
    si: int
    di: int
    s: int

  KKS = seq[KK]

proc fillInPri(s: var seq[KK]; el: KK): bool {.inline.} =
  for i in mitems(s):
    if i.di == el.di and i.si == el.si:
      i.s = el.s
      return true
  false

proc isort(a: var seq[KK]) {.inline.} =
  for i in 1 .. high(a):
    let x = a[i]
    var j = i - 1
    while j >= 0 and a[j].s < x.s:
      a[j + 1] = a[j]
      dec j
    a[j + 1] = x

proc capture(kk: KK): bool {.inline.} = kk.sf * kk.df < 0

proc valid(kk: KK): bool {.inline.} = kk.sf * kk.df <= 0

proc wanted(kk: KK): bool {.inline.} = kk.sf * kk.df < (kk.s > 0).int

const
  KingWalkGain = 1
  KingControlGain = 2
  QueenWalkGain = 1
  QueenControlGain = 2
  RookWalkGain = 1
  RookControlGain = 2
  BishopWalkGain = 1
  BishopControlGain = 2
  KnightWalkGain = 1
  KnightControlGain = 2
  PawnWalkGain = 1
  PawnControlGain = 3

proc walkRook(kk: KK; s: var KKS; mobLevel: int = MaxMob) {.inline.} =
  var i: int
  var kk = kk
  while (kk.di := rookPath[kk.si][i].pos) >= 0:
    if (kk.df := board[kk.di]) == 0:
      inc i
      boardControl[mobLevel] += RookWalkGain
    else:
      i = rookPath[kk.si][i].nxtDirIdx
      boardControl[mobLevel] += RookControlGain
    if wanted(kk): s.add kk

proc walkBishop(kk: KK; s: var KKS; mobLevel: int = MaxMob) {.inline.} =
  var i: int
  var kk = kk
  while (kk.di := bishopPath[kk.si][i].pos) >= 0:
    if (kk.df := board[kk.di]) == 0:
      inc i
      boardControl[mobLevel] += BishopWalkGain
    else:
      i = bishopPath[kk.si][i].nxtDirIdx
      boardControl[mobLevel] += BishopControlGain
    if wanted(kk): s.add kk

proc walkKing(kk: KK; s: var KKS; mobLevel: int = MaxMob) {.inline.} =
  var kk = kk
  for i in 0 .. 7:
    if (kk.di := kingPath[kk.si][i].pos) < 0: break
    if (kk.df := board[kk.di]) == 0:
      boardControl[mobLevel] += KingWalkGain
    else:
      boardControl[mobLevel] += KingControlGain
    if wanted(kk):
      s.add kk

proc walkKnight(kk: KK; s: var KKS; mobLevel: int = MaxMob) {.inline.} =
  var kk = kk
  for i in 0 .. 7:
    if (kk.di := knightPath[kk.si][i].pos) < 0: break
    if (kk.df := board[kk.di]) == 0:
      boardControl[mobLevel] += KnightWalkGain
    else:
      boardControl[mobLevel] += KnightControlGain
    if wanted(kk):
      s.add kk

proc walkPawn(kk: KK; s: var KKS; mobLevel: int = MaxMob) {.inline.} =
  var kk = kk
  let colIdx = (kk.sf + 1) div 2
  for i in 0..1:
    if (kk.di := pawnPath[colIdx][kk.si][i].pos) >= 0:
      boardControl[mobLevel] += PawnControlGain
      kk.df = board[kk.di]
      if capture(kk) or (kk.s >= 0 and row2or5(kk.di) and kk.s in mobSet[kk.di]): # > 11 is OK
        #boardControl[mobLevel] += PawnControlGain
        s.add kk
  #if kk.s > 0: # XXX try >= 0 instead of > now!
  if kk.s >= 0: # XXX try >= 0 instead of > now!
    for i in 2..3:
      if (kk.di := pawnPath[colIdx][kk.si][i].pos) >= 0:
        if (kk.df := board[kk.di]) == 0:
          boardControl[mobLevel] += PawnWalkGain
          s.add kk
        else: break

type
  Move = tuple
    src: int
    dst: int
    score: int
    checkmateDepth: int

var evCounter: int

# note:   assert (color == White) == ((mobLevel and 1) == 0)
# result is for White
proc evaluateBoard(mobLevel: int): int {.inline.} =
  evCounter += 1
  for p, f in board:
    # if f != 0: # that makes it slower
    result += (FigureValue[f.abs] + freedom[f][p]) * sign(f)
  var v = boardControl[mobLevel] - boardControl[mobLevel + 1]
  if (mobLevel and 1) != 0:
    v = -v
  return result + v

proc plainEvaluateBoard: int {.inline.} =
  evCounter += 1
  for p, f in board:
    # if f != 0: # that makes it slower
    result += (FigureValue[f.abs] + freedom[f][p]) * sign(f)

proc smartEvaluateBoard(mobLevel: int): int {.inline.} =
  result = boardControl[mobLevel] - boardControl[mobLevel + 1]
  if (mobLevel and 1) != 0:
    result = -result

discard """
https://chessprogramming.wikispaces.com/Alpha-Beta
int alphaBeta( int alpha, int beta, int depthleft ) {
   if( depthleft == 0 ) return quiesce( alpha, beta );
   for ( all moves)  {
      score = -alphaBeta( -beta, -alpha, depthleft - 1 );
      if( score >= beta )
         return beta;   //  fail hard beta-cutoff
      if( score > alpha )
         alpha = score; // alpha acts like max in MiniMax
   }
   return alpha;
}
"""
proc inCheck(si: int; col: Color): bool =
  var
    kk {.noInit.}: KK
    s {.global.} = newSeqOfCap[KK](8)
  kk.si = si
  kk.sf = sign(col.int)
  assert kk.sf == col.int
  kk.s = -1 # only captures
  s.clear
  walkBishop(kk, s)
  if anyIt(s, it.df.abs == BishopID or it.df.abs == QueenID): return true
  s.clear
  walkRook(kk, s)
  if anyIt(s, it.df.abs == RookID or it.df.abs == QueenID): return true
  s.clear
  walkKnight(kk, s)
  if anyIt(s, it.df.abs == KnightID): return true
  s.clear
  walkPawn(kk, s)
  if anyIt(s, it.df.abs == PawnID): return true
  s.clear
  walkKing(kk, s)
  return anyIt(s, it.df.abs == KingID)

proc stalemate(s: KKS; color: Color; kp: int): bool {.inline.} =
  if anyIt(s, it.sf.abs != KingID): return false
  if inCheck(kp, color): return false
  if anyIt(s, not inCheck(it.di, color)): return false
  return true

proc freePieces(color: Color): bool {.inline.} =
  for i, f in board:
    if f * color.int > 0:
      if f.abs != KingID and f.abs != PawnID: return true
      if f.abs == PawnID and board[i + color.int * 8] == VoidID: return true
  return false

proc kingPos(c: Color): Position {.inline.} =
  let k = KingID * c.int
  for i, f in board:
    if f == k:
      return i

proc stopgame(s: KKS; color: Color): bool =
  if anyIt(s, it.sf.abs != KingID): return false
  if anyIt(s, not inCheck(it.di, color)): return false
  return true


var
  qsucc, qtot: int64


const QD0 = 0
proc quiescence(color: Color; depthleft, mobLevel: int; alpha0: int; beta: int): int =
  var
    hashRes {.noInit.}: HashResult
    kk {.noInit.}: KK
    si, di: int
    alpha = alpha0
    hashPos = -1
    enPassant {.noInit.}: bool
    kingpos: int

  let nexMob = mobLevel - 1
  assert(depthleft <= 0)
  let hhh = encodeBoard(color, QD0).data
  hashPos = getTTE(hhh, hashRes)
  inc(qtot)
  if hashPos >= 0:
    inc(qsucc)
    #let yyy = if ENDG: QD0 else: MaxDepth # not necessary any more due to history!
    for i in countdown(MaxDepth, QD0):
      if hashRes.score[i].v > low(int16):
        return hashRes.score[i].v
      if hashRes.floor[i].v >= beta:
        return beta
  else:
    initHR(hashRes)

  var state: int
  #when true:#if depthleft < 0:
  #if depthleft < 0:
  state = plainEvaluateBoard() * color.int
  if state >= beta + 15:
    return beta
  #stdout.write($state & 'x')
  #if alpha < state: alpha = state
  var s = newSeqOfCap[KK](2) # captures

  kk.s = mobLevel
  if depthleft < 0:
    kk.s = -1
  boardControl[mobLevel] = 0
  for si, sf in board: # source index, source figure
    if sf * color.int <= 0: continue
    kk.si = si
    kk.sf = sf
    case sf.abs:
      of PawnID: walkPawn(kk, s, mobLevel)
      of KnightID: walkKnight(kk, s, mobLevel)
      of BishopID: walkBishop(kk, s, mobLevel)
      of RookID: walkRook(kk, s, mobLevel)
      of QueenID: walkBishop(kk, s, mobLevel); walkRook(kk, s, mobLevel)
      of KingID: walkKing(kk, s, mobLevel); kingpos = si
      else: discard

  #if depthleft < 0:
  state += smartEvaluateBoard(mobLevel) * color.int
  #else:
  #  state = evaluateBoard(mobLevel) * color.int
  if state >= beta:
    return beta
  if alpha < state: alpha = state

  if ENDG and not freePieces(color) and stalemate(s, color, kingpos): # this test is only really necessary in endgame
    kk.s = 1
    kk.si = kingpos
    kk.sf = board[kingpos]
    walkKing(kk, s)
    if stalemate(s, color, kingpos):
      let h = -evaluateBoard(mobLevel) * color.int
      if h >= beta:
        return beta
      if h > alpha:
        alpha = h
      return alpha

  for i, el in s.mpairs: # guess of score for sorting
    el.s = FigureValue[el.df.abs] - FigureVax[el.sf.abs]

  if hashPos >= 0:
    for i in countdown(MaxDepth, QD0):
      if hashRes.floor[i].v > low(int16):
        kk.si = hashRes.floor[i].si
        kk.di = hashRes.floor[i].di
        kk.s = 2 * i + QueenValue
        if not s.fillInPri(kk) and depthleft > -3:
          kk.sf = board[kk.si]
          kk.df = board[kk.di]
          s.add(kk)

    when false: #ENDG: # otherwise the higher lewels are already queried
      for i in countdown(MaxDepth, QD0 + 1):
        if hashRes.score[i].v > low(int16):
          kk.si = hashRes.score[i].si
          kk.di = hashRes.score[i].di
          kk.s = 2 * i + QueenValue + 1
          if not s.fillInPri(kk) and depthleft > -3:
            kk.sf = board[kk.si]
            kk.df = board[kk.di]
            s.add(kk)

  s.isort
  for el in s:
    if el.df.abs == KingID: return KingValue + depthleft * 1024 # ~QueenValue
    board[el.si] = VoidID
    board[el.di] = el.sf
    if baseRow(el.di):
      enPassant = false
      if el.sf.abs == PawnID:
        board[el.di] *= QueenID
    else:
      enPassant = el.sf.abs == PawnID and el.df == VoidID and (el.di - el.si).odd # move is an eP capture
      if enPassant: board[el.di - color.int * 8] = VoidID
    let score = -quiescence(color.oppColor, depthleft - 1, nexMob, -beta, -alpha)
    board[el.di] = el.df
    board[el.si] = el.sf
    if enPassant: board[el.di - color.int * 8] = -el.sf
    if score >= beta:
      if hashRes.floor[QD0].v < score:
        hashRes.floor[QD0].v = score.int16
        hashRes.floor[QD0].si = el.si.int8
        hashRes.floor[QD0].di = el.di.int8
        if hashPos >= 0:
          hashRes.pri = depthleft
          tt[hashPos].res = hashRes
        else:
          putTTE(hhh, hashRes, depthleft)
      return beta
    if score > alpha:
      alpha = score
      si = el.si
      di = el.di

  if alpha > alpha0 and (si != 0 or di != 0):
    if hashRes.score[QD0].v < alpha:
      hashRes.score[QD0].v = alpha.int16
      hashRes.score[QD0].si = si.int8
      hashRes.score[QD0].di = di.int8
      if hashPos >= 0:
        hashRes.pri = depthleft
        tt[hashPos].res = hashRes
      else:
        putTTE(hhh, hashRes, depthleft)
  return alpha

const
  VRatio = 8
  SDI = [0, 0, 0, 0, 0, 0, 4] # source figure depth increase # increase depth when king is moved
  DDI = [0, 2, 4, 4, 4, 4, 0] # destination figure depth increase # increase depth for capture

  #SDI = [0, 0, 0, 0, 0, 0, 0]
  #DDI = [0, 0, 0, 0, 0, 0, 0]



# moblevel and vdepth:
# moblevel is used for en passant pawn moves and for indicating attacked positions for castling
# moblevel starts at 15 and decreases by one for each call of alphabeta()
# vdepth is the virtual search depth, it is a multiple of real search depth to allow a more
# fine grained search depth extension.
# vdepth starts with a multiple of VRatio (n * VRation + VRatio div 2), and generally decreases by
# VRatio for each call of alphabeta(). For special very important moves it may decrease less,
#  i.e. if we are in check. Real depth is always vdepth div VRatio.
# While moblevel deceases by one for each call of alphabeta(), vdepth may even increase in rare cases!


var
  asucc, atot: int64

proc alphabeta(color: Color; vdepth: int; moblevel: int; alpha0: int; beta: int): Move =

  assert (color == White) == ((mobLevel and 1) == 0)


  assert(MaxDepth == 15)
  assert(VRatio == 8)
  assert(moblevel in {0 .. MaxDepth})
  var nextmob = moblevel - 1 ### make it a let TODO
  let depth = vdepth div VRatio
  if depth <= 0 or moblevel == 0:
    result.score = quiescence(color, 0, nextMob, alpha0, beta)
    return

  var
    hashRes{.noinit.}: HashResult
    kk{.noinit.}: KK
    sdi, ddi: array[7, int]
    hashPos = -1
    enPassant{.noInit.}: bool
    alpha = alpha0
    vdepth = vdepth


  assert(moblevel in {1 .. MaxDepth})
  let kingPos = kingPos(color)
  let inCh = inCheck(kingpos, color) # expensive, but useful for depth extension
  if ENDG or not inCh:
    vdepth -= VRatio
    if not ENDG:
      sdi = SDI
      ddi = DDI

  #if vdepth < VRatio:
  #  nextmob = 0 # next call is quiesc(), we set bit 0 in mobset for ep, so quiesc() can test for ep capture.

  ###let hhh = encodeBoard(color, depth).data
  let hhh = encodeBoard(color, mobLevel).data
  hashPos = getTTE(hhh, hashRes)
  inc(atot)
  if hashPos >= 0:
    inc(asucc)
    #let yyy = if ENDG: depth else: MaxDepth
    for i in countdown(MaxDepth, depth):
      if hashRes.score[i].v > low(int16):
        result.score = hashRes.score[i].v
        result.src = hashRes.score[i].si
        result.dst = hashRes.score[i].di
        result.checkmateDepth = i # return depth info for checkmate result from table
        return
      if hashRes.floor[i].v >= beta:
        result.score = beta
        result.src = hashRes.floor[i].si
        result.dst = hashRes.floor[i].di
        return
  else:
    initHR(hashRes)

  var s = newSeqOfCap[KK](64)
  var popCnt = 0
  #kk.s = depth
  kk.s = mobLevel
  boardControl[mobLevel] = 0
  for si, sf in board: # source index, source figure
    inc(popCnt)
    if sf * color.int <= 0: continue
    kk.si = si
    kk.sf = sf
    case sf.abs:
      of PawnID: walkPawn(kk, s, mobLevel)
      of KnightID: walkKnight(kk, s, mobLevel)
      of BishopID: walkBishop(kk, s, mobLevel)
      of RookID: walkRook(kk, s, mobLevel)
      of QueenID: walkBishop(kk, s, mobLevel); walkRook(kk, s, mobLevel)
      of KingID: walkKing(kk, s, mobLevel); assert(kk.si == kingpos)
      else: discard

  if ENDG and not inCh and stalemate(s, color, kingpos): # this test is only really necessary in endgame
  #if not inCh  and stalemate(s, color, kingpos):
    let h = -evaluateBoard(mobLevel) * color.int # maybe just h = QueenValue
    result.checkmateDepth = StalemateMarker
    if h >= beta:
      result.score = beta # or return m.score? should not really matter
      return
    if h > alpha:
      alpha = h
    result.score = alpha
    return

  for i, el in s.mpairs: # guess of score for sorting
    el.s = FigureValue[el.df.abs] - FigureVax[el.sf.abs]
    assert(el.s == FigureValue[el.df.abs].abs - FigureVax[el.sf.abs].abs)

  if hashPos >= 0: # fix score for moves contained in transposition table
    for i in countdown(MaxDepth, QD0):
      if hashRes.floor[i].v > low(int16):
        kk.si = hashRes.floor[i].si
        kk.di = hashRes.floor[i].di
        kk.s = 2 * i + QueenValue
        if not (isAKing(kk.si) and (kk.si - kk.di).abs == 2): # castling is not in seq
          if not s.fillInPri(kk): ########################################################################################
            # echo kk # caution: kk can be an ep capture, which is not contained in s! we have to think about it.
            # assert(false)
            discard
    #for i in countdown(MaxDepth, QD0): # MaxDepth .. depth was already used below!
    for i in countdown(depth - 1, QD0): # but this is not faster!
      if hashRes.score[i].v > low(int16):
        kk.si = hashRes.score[i].si
        kk.di = hashRes.score[i].di
        kk.s = 2 * i + QueenValue + 1
        if not (isAKing(kk.si) and (kk.si - kk.di).abs == 2):
          if not s.fillInPri(kk):
            assert(false)

  s.isort
  if hashPos < 0 and depth > 3: # fast search for good move ordering
    for el in s.mitems:
      if el.df.abs == KingID: el.s = KingValue; break
      board[el.si] = VoidID
      board[el.di] = el.sf
      if baseRow(el.di):
        enPassant = false
        if el.sf.abs == PawnID:
          board[el.di] *= QueenID
        incl(mobSet[el.di], moblevel) # we attack this square in base row
      else:
        enPassant = el.sf.abs == PawnID and el.df == VoidID and (el.di - el.si).odd # move is an eP capture
        if enPassant: board[el.di - color.int * 8] = VoidID
      let h = hasMoved[el.si]
      hasMoved[el.si] = true # may be a king or rook move, so castling is forbidden
      let pawnJump = el.sf.abs == PawnID and (el.si - el.di).abs == 16
      if pawnJump: incl(mobSet[(el.si + el.di) div 2], nextmob) # next opp move can do eP capture
      var m = alphabeta(color.oppColor, vdepth - 3 * VRatio, nextmob, -beta, -alpha)
      if pawnJump: excl(mobSet[(el.si + el.di) div 2], nextmob)
      hasMoved[el.si] = h
      board[el.di] = el.df
      board[el.si] = el.sf
      if enPassant: board[el.di - color.int * 8] = -el.sf
      m.score *= -1
      el.s = m.score + 2 * QueenValue # for move ordering, put these on top
      if m.score >= beta:
        break
      if m.score > alpha:
        alpha = m.score
    s.isort
  alpha = alpha0
  for el in s:
    if el.df.abs == KingID:
      result.score = KingValue + depth * QueenValue
      result.src = el.si
      result.dst = el.di
      return
    board[el.si] = VoidID
    board[el.di] = el.sf
    if baseRow(el.di):
      enPassant = false
      if el.sf.abs == PawnID:
        board[el.di] *= QueenID
      incl(mobSet[el.di], mobLevel)#depth) # we attack this square ???????????????????? mobLevel?
    else:
      enPassant = el.sf.abs == PawnID and el.df == VoidID and (el.di - el.si).odd # move is an eP capture
      if enPassant: board[el.di - color.int * 8] = VoidID
    let h = hasMoved[el.si]
    hasMoved[el.si] = true # may be a king or rook move, so castling is forbidden
    let pawnJump = el.sf.abs == PawnID and (el.si - el.di).abs == 16
    if pawnJump: incl(mobSet[(el.si + el.di) div 2], nextmob) # next opp move can do eP capture


    #if pawnPressure[el.si, moblevel + 2]:
    let regDepth = vdepth
    if el.sf.abs == PawnID:
      var pawnDepthInc = VRatio div 2
      if popCnt < 32:
        pawnDepthInc = VRatio
      if rowsToGo(el.si, color) == 6 and (el.si - el.di).abs == 8:
        pawnDepthInc = 0
      incl(pawnPressure[el.di], mobLevel)
      if  rowsToGo(el.si, color) < 5:
        if (moblevel + 2) <= MaxDepth and (moblevel + 2) in pawnPressure[el.si] or
          (moblevel + 4) <= MaxDepth and (moblevel + 4) in pawnPressure[el.si]:
          vdepth += pawnDepthInc


    var m: Move
    if el.sf.abs == PawnID or el.df != VoidID:
      m = alphabeta(color.oppColor, vdepth + sdi[el.sf.abs] + ddi[el.df.abs], nextmob, -beta, -alpha)
    else: # deal with repetive positions
      let newState = encodeBoard(color, -1).data
      if history.contains(newState):
        if evaluateBoard(mobLevel) * color.int < -BishopValue: # our position is weak, so we favour draw by rep.
          m.score = -QueenValue # sign is inverted below!
        else:
          m.score = QueenValue
      else:
        history.incl(newState)
        m = alphabeta(color.oppColor, vdepth + sdi[el.sf.abs] + ddi[el.df.abs], nextmob, -beta, -alpha)
        history.excl(newState)
    m.score *= -1

    excl(pawnPressure[el.di], mobLevel)
    vdepth = regDepth

    if pawnJump: excl(mobSet[(el.si + el.di) div 2], nextmob)
    hasMoved[el.si] = h
    board[el.di] = el.df
    board[el.si] = el.sf
    if enPassant: board[el.di - color.int * 8] = -el.sf
    if m.score >= beta:
      #m.score += 100

      #result.src = el.si # should be never used!
      #result.dst = el.di
      #[ it is sufficient to fill in the score only for level depth, because query starts with MaxDepth!
      var put = false
      #let yyy = if ENDG: depth else: QD0
      let yyy = QD0
      for i in countup(yyy, depth):
        if hashRes.floor[i].v < m.score:
          put = true
          hashRes.floor[i].v = m.score.int16
          hashRes.floor[i].si = el.si.int8
          hashRes.floor[i].di = el.di.int8
        if put:
          if hashPos >= 0:
            hashRes.pri = depth
            tt[hashPos].res = hashRes
          else:
            putTTE(hhh, hashRes, depth) # we could optimize by just using index from getTTE()
          result.score = beta # or return m.score? should not really matter
          ]#
      if hashRes.floor[depth].v < m.score:
        hashRes.floor[depth].v = m.score.int16
        hashRes.floor[depth].si = el.si.int8
        hashRes.floor[depth].di = el.di.int8
        if hashPos >= 0:
          hashRes.pri = depth
          tt[hashPos].res = hashRes
        else:
          putTTE(hhh, hashRes, depth)
      result.score = beta # or return m.score? should not really matter
      return
    if m.score > alpha:
      alpha = m.score
      result.src = el.si
      result.dst = el.di

  if not inCh:
    const # king, void, void, void, rook, kingDelta, rookDelta
      Q = [[3, 2, 1, 1, 0, -2, 2], [3, 4, 5, 6, 7, 2, -3]]
    let
      k = WKing * color.int
      r = WRook * color.int
    for i in 0..1: # castlings both sides
      var q = Q[i]
      if color == Black:
        for j in 0..4:
          q[j] += 7 * 8
      if board[q[0]] == k and board[q[1]] == 0 and board[q[2]] == 0 and board[q[3]] == 0 and board[q[4]] == r and
        not (hasMoved[q[0]] or hasMoved[q[4]]):
        #echo "Rochade aaa"
        hasMoved[q[0]] = true # ; hasMoved[q[4]] = true # not really necessary
        board[q[0]] = 0
        board[q[0] + q[5]] = k
        board[q[4] + q[6]] = r
        board[q[4]] = 0
        excl(mobSet[q[0]], nextmob); excl(mobSet[q[1]], nextmob); excl(mobSet[q[2]], nextmob) # attacked positions, opp moves will set these
        #var m = alphabeta(color.oppColor, x, -beta, AB_inf) # full width search with max beta to set really all attack bits
        var m = alphabeta(color.oppColor, vdepth, nextmob, -beta, -alpha) # maybe better do prunning and use inCheck() as below?
        hasMoved[q[0]] = false # ; hasMoved[q[4]] = false
        board[q[0]] = k
        board[q[1]] = 0
        board[q[2]] = 0
        board[q[3]] = 0
        board[q[4]] = r
        m.score *= -1
        assert(beta > alpha)
        #echo "ccc", m.score, " " , alpha
        if m.score > alpha:
          echo "Rochade bbb"
          if not (nextmob in mobSet[q[0]] or nextmob in mobSet[q[1]] or nextmob in mobSet[q[2]]): # was castling legal?
            echo "Rochade ccc"
            #if not (inCheck(q[1], color) or inCheck(q[2], color)): # we have to check again due to prunning
            if not inCheck(q[1], color): # well only check of q[1] is necessary, other is ordinary illegal in check case
              echo "Rochade"
              if m.score >= beta:
                # now we put this into transposition table too, but there should be not much benefit
                #result.src = q[0]
                #result.src = q[0] + q[5]
                if hashRes.floor[depth].v < m.score:
                  hashRes.floor[depth].v = m.score.int16
                  hashRes.floor[depth].si = q[0].int8
                  hashRes.floor[depth].di = (q[0] + q[5]).int8
                  if hashPos >= 0:
                    hashRes.pri = depth
                    tt[hashPos].res = hashRes
                  else:
                    putTTE(hhh, hashRes, depth)
                result.score = beta # or return m.score? should not really matter
                return
              if m.score > alpha:
                alpha = m.score
                result.src = q[0]
                result.dst = q[0] + q[5]

  result.checkmateDepth = depth
  if alpha < -SureCheckmate and stopgame(s, color):
    result.checkmateDepth = StopGameMarker
  elif alpha > alpha0:
    assert result.src != 0 or result.dst != 0
    #[ it is sufficient to fill in the score only for level depth, because query starts with MaxDepth!
    var put = false
    #let yyy = if ENDG: depth else: QD0
    let yyy = QD0
    for i in countup(yyy, depth):
      if hashRes.score[i].v < alpha:
        put = true
        hashRes.score[i].v = alpha.int16
        hashRes.score[i].si = result.src.int8
        hashRes.score[i].di = result.dst.int8
      if put:
        if hashPos >= 0:
          hashRes.pri = depth
          tt[hashPos].res = hashRes
        else:
          putTTE(hhh, hashRes, depth)
        ]#
    if hashRes.score[depth].v < alpha:
      hashRes.score[depth].v = alpha.int16
      hashRes.score[depth].si = result.src.int8
      hashRes.score[depth].di = result.dst.int8
      if hashPos >= 0:
        hashRes.pri = depth
        tt[hashPos].res = hashRes
      else:
        putTTE(hhh, hashRes, depth)
  result.score = alpha
  #if alpha > alpha0:
  #  result.score += 100

type Flag* {.pure.} = enum
  plain, capture, ep, promotion, procap

proc doMove*(p0, p1: Position; silent = false): Flag =
  if not isVoid(p1): result = Flag.capture
  if not silent:
    hasMoved[p0] = true
    pjm = -1
    if isAPawn(p0) and (p0 - p1).abs == 16:
      pjm = (p0 + p1) div 2
  if (p1 - p0).abs == 2 and isAKing(p0):
    if col(p1) == 1:
      board[p0 - 1] = board[p0 - 3]
      board[p0 - 3] = VoidID
    else:
      board[p0 + 1] = board[p0 + 4]
      board[p0 + 4] = VoidID
  elif baseRow(p1) and isAPawn(p0):
    board[p0] *= QueenID
    result = if result == Flag.capture: Flag.procap else: Flag.promotion
  elif isAPawn(p0) and isVoid(p1) and (p1 - p0).odd:
    result = Flag.ep
    board[p1 - board[p0] * 8] = VoidID
  board[p1] = board[p0]
  board[p0] = VoidID
  if not silent:
    if isAPawn(p1) or result != Flag.plain:
      history = initHashSet[array[24, int8]]()
    else:
      let newState = encodeBoard(sign(board[p1]).Color, -1).data
      history.incl(newState)

proc tag*(si: int): KKS =
  var kk {.noInit.}: KK
  kk.sf = board[si]
  let color = sign(kk.sf).Color
  kk.si = si
  kk.s = 1 # generate all moves, not only captures
  var s = newSeqOfCap[KK](32)
  case kk.sf.abs:
    of PawnID: walkPawn(kk, s)
    of KnightID: walkKnight(kk, s)
    of BishopID: walkBishop(kk, s)
    of RookID: walkRook(kk, s)
    of QueenID: walkBishop(kk, s); walkRook(kk, s)
    of KingID: walkKing(kk, s)
    else: discard
  if si == 3 or si == 3 + 7 * 8:
    const # king, void, void, void, rook, kingDelta, rookDelta
      Q = [[3, 2, 1, 1, 0, -2, 2], [3, 4, 5, 6, 7, 2, -3]]
    let
      k = WKing * color.int
      r = WRook * color.int
    for i in 0..1: # castlings both sides
      var q = Q[i]
      if color == Black:
        for j in 0..4:
          q[j] += 7 * 8
      if board[q[0]] == k and board[q[1]] == 0 and board[q[2]] == 0 and board[q[3]] == 0 and board[q[4]] == r and
        not (hasMoved[q[0]] or hasMoved[q[4]]):
        if not (inCheck(q[1], color) or inCheck(q[2], color)):
          kk.di = q[0] + q[5]
          s.add kk
  let backup = board
  for el in s.mitems:
    discard doMove(si, el.di, silent = true)
    if inCheck(kingPos(color), color): el.s = 0
    board = backup
  keepIf(s, proc(el: KK): bool = el.s != 0)
  return s

proc moveIsValid*(si, di: int): bool {.inline.} =
  sign(board[si]).Color == White and anyIt(tag(si), it.di == di)

const
  FigStr = ["  ", "  ", "N_", "B_", "R_", "Q_", "K_"]

proc colStr(c: Col): char {.inline.} = char('H'.int - c.int)

proc rowStr(c: Col): char {.inline.} = char('1'.int + c.int)

proc getBoard*: Board {.inline.} =
  result = board

# call this after doMove()
proc moveToStr*(si, di: Position; flag: Flag): string =
  when true: # moveIsValid(si, di): # avoid unnecessary expensive test
    if board[di].abs == KingID and (di - si).abs == 2:
      result = if col(di) == 1: "o-o" else: "o-o-o"
    else:
      result = FigStr[board[di].abs]
      result.add(colStr(col(si)))
      result.add(rowStr(row(si)))
      result.add(if flag == Flag.capture or flag == Flag.procap: 'x' else: '-')
      result.add(colStr(col(di)))
      result.add(rowStr(row(di)))
      if flag == Flag.ep or flag == Flag.procap:
        result.add(" e.p.")
    if inCheck(kingPos((-sign(board[di])).Color), (-sign(board[di])).Color):
      result.add(" +")
  else:
    result = "invalid move"

# Endgame = no pawns, weaker side has no queen, no rook and not two bishops.
proc setupEndgame: bool {.inline.} =
  var
    p: array[-KingID..KingID, int]
    h: array[-1..1, int] # total number of pieces
    b: array[-1..1, int] # single bishop position
  for i, f in board:
    p[f] += 1
    h[sign(f)] += 1
    if f.abs == BishopID: b[sign(f)] = i
  if p[WPawn] + p[BPawn] > 0: return
  if h[-1] > 3 or h[1] > 3: return
  for i in BKing .. WKing:
    for j in PosRange: freedom[i][j] = 0
  for s in [-1, 1]: # black, white -- set the hunting matrix for opposite king
    if p[QueenID * s] + p[RookID * s] == 0 and p[BishopID * s] + p[KnightID * s] < 2:
      continue # of course with only two knights it is hard, but one may try.
    let oppKing = -s * KingID
    for i in PosRange:
      if p[QueenID * s] + p[RookID * s] == 0 and p[BishopID * s] < 2: # chase to selected corner
        if col(b[s]).odd != row(b[s]).odd:
          freedom[oppKing][i] = -(row(i) - col(i)).sqr # sqr may be better than abs when both sites are
        else: # struggling, i.e. K + B + B vs K + B
          freedom[oppKing][i] = -(row(i) + col(i) - 7).sqr
      else: # chase to border and/or arbitrary corner
        freedom[oppKing][i] = -((2 * row(i) - 7).abs + (2 * col(i) - 7).abs div 2).sqr
    #if s == -1: echo "White King" else: echo "Black King"
    #for i, f in board:
    #  if i mod 8 == 0: echo("")
    #  write(stdout, $freedom[oppKing][i]); write(stdout, " ");
    #echo ""
  return true

proc reply*: Move {.noinit.} =
  const
    Time = 5      # seconds
    ABWindow = 32 # size seems to make no big difference
  var
    hashRes {.noinit.}: HashResult
    #lastbest {.noinit.}: Move
    alpha = -AB_Inf
    beta = AB_inf
    depth = 0

  qsucc = 0
  qtot = 0
  asucc = 0
  atot = 0

  let startTime = cpuTime()
  #lastbest.score = low(int)
  if setupEndgame():
    if not ENDG: # endgame does not work well when table contains deep knowledge
      ENDG = true
  let hhh = encodeBoard(Black, depth).data
  if getTTE(hhh, hashRes) >= 0:
    block abeta:
      for i in countdown(MaxDepth, 0): # only i == depth - 1 ?
        if hashRes.score[i].v > low(int16):
          alpha = hashRes.score[i].v - ABWindow
          beta = alpha + 2 * ABWindow
          break abeta
      for i in countdown(MaxDepth, 0): # only i == depth ?
        if hashRes.floor[i].v > low(int16):
          alpha = hashRes.floor[i].v - ABWindow
          break abeta
  echo GC_getStatistics()
  for el in mitems(tt): el.res.pri = low(int)
  while depth < MaxDepth:
    inc depth
    echo "Depth: ", depth
    #if pjm > 0: incl(mobSet[pjm], depth)
    var abInc = ABWindow
    while true:
      abInc *= 2
      result = alphabeta(Black, depth * VRatio + VRatio div 2, MaxDepth, alpha, beta)
      if result.score <= alpha:
        alpha -= abInc
      elif result.score >= beta:
        beta += abInc
      else:
        #if result.score > lastbest.score:
        #  lastbest = result
        break
    if pjm > 0: excl(mobSet[pjm], depth)
    echo "score: ", result.score, "(", result.src, "-", result.dst, ")"
    if result.score.abs > SureCheckmate:
      break
    if cpuTime() - startTime > Time: #or depth > 3:
      echo "Time: ", cpuTime() - startTime
      echo "cols rate: ", iscol / (iscol + nocol), " ", iscol, ' ', nocol, ' ', evCounter
      echo "qsucc / qtot: ", qsucc.float / qtot.float
      echo "asucc / atot: ", asucc.float / atot.float
      break
    alpha = result.score - ABWindow
    beta = alpha + 2 * ABWindow
  #if ENDG:
  #  result = lastbest
  if result.checkmateDepth == StalemateMarker or result.checkmateDepth == StopGameMarker:
    discard
  elif result.score > SureCheckmate:
    result.checkmateDepth = (result.checkmateDepth - 2) div 2
  elif result.score < SureCheckmate:
    result.checkmateDepth = (result.checkmateDepth - 1) div 2

proc setBoard(f: FigureID; c, r: Position) = board[c + r * 8] = f

proc print =
  for p, f in board:
    if p mod 8 == 0:
      echo ""
    if f >= 0:
      write(stdout, ' ')
    write(stdout, $f & "|" & $p & ' ')
    if p < 10: echo ' '
  echo ""

#proc setHappyness(f: FigureID; c, r: Position; h: int) = freedom[f][c + r * 8] = h

initPawn(White)
initPawn(Black)
initBishop()
initKnight()
initKing()
initRook()
board = Setup
when not defined(release):
  print()
#checkmateDepth = -1
#setBoard(BKing, BC, B4)
#setBoard(WKing, BD, B5)
#setBoard(BBishop, BD, B4)
#setBoard(BKnight, BD, B3)
#setBoard(WKnight, BA, B2)
#setBoard(WBishop, BG, B3)
#setHappyness(PawnID, BE, B5, 75)

#setBoard(BKing, BC, B4)
#setBoard(WKing, BC, B3)
#setBoard(BBishop, BD, B4)
#setBoard(BBishop, BD, B3)

when isMainModule:
  echo "use board.nim"
# 1234 + 0 fasterWriteToBitBuffer pawnPressure encodeBoard
#score: -7(51-35)
#Time: 22.259099223 cols
