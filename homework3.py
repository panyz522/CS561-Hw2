import sys, math, time, os, pickle, copy
datafilename = "playdata.txt"
fixedTimeC = 3.3e-7
startTime = time.time()

DEBUG = True
IGNORETIME = True
def debug(*args):
    print(*args)

class GameTimeoutError(TimeoutError):
    def __init__(self, res):
        self.res = res

# Input and output
class IO:
    def __init__(self, filename, mode):
        self.file = open(filename, mode)

    def close(self):
        self.file.close()

    def rdRaw(self):
        if self.file is None:
            return input()
        return self.file.readline()

    def rdSingle(self, tp):
        return tp(self.rdRaw())

    def rdList(self, tp):
        line = self.rdRaw()
        line = line.strip('\n')
        line = list(map(tp, list(line[:16])))
        return line

    def rdMat(self, tp, n):
        mat = []
        for _ in range(n):
            mat.append(self.rdList(tp))
        return mat

    def wtLine(self, slist, delim):
        self.file.write(delim.join(slist) + '\n')

    def wtRes(self, resarr: list):
        self.file.write('\n'.join(map(str, resarr)))

    @staticmethod
    def rdObjIfValid():
        if (not os.path.exists(datafilename)):
            return None
        with open(datafilename, "rb") as f:
            try:
                obj = pickle.load(f)
                debug("Data Loaded", datafilename)
            except:
                debug("Pickle load failed")
            if isinstance(obj, list) and len(obj) > 0:
                return obj
            return None
    @staticmethod
    def wtObj(obj):
        with open(datafilename, "wb") as f:
            debug("Data Saved", datafilename)
            obj = pickle.dump(obj, f)
    @staticmethod
    def rmObjFile():
        os.remove(datafilename)

class TupleOp:
    @staticmethod
    def addt(t1, t2):
        return (t1[0] + t2[0], t1[1] + t2[1])
    @staticmethod
    def subt(t1, t2):
        return (t1[0] - t2[0], t1[1] + t2[1])
    @staticmethod
    def addi(t, v):
        return (t[0] + v, t[1] + v)
    @staticmethod
    def rev(t):
        return (-t[0], -t[1])

class Move:
    def __init__(self, mtype: str, st, ed):
        self.mtype = mtype
        self.st = st
        self.ed = ed
    def __repr__(self):
        return "(%s %s,%s %s,%s)" % (self.mtype, self.st[0], self.st[1], self.ed[0], self.ed[1])
    def __str__(self):
        return "%s %s,%s %s,%s" % (self.mtype, self.st[1], self.st[0], self.ed[1], self.ed[0])

class Solution:
    def __init__(self):
        self.edirs4w = ((-1, -1), (0, -1), (-1, 0), (1, -1), (-1, 1), (1, 0), (0, 1), (1, 1))
        self.edirs4b = self.edirs4w[::-1]
        self.lefttops = set([(0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, 0), (2, 1), (2, 2), (2, 3), (3, 0), (3, 1), (3, 2), (4, 0), (4, 1)])
        self.rightbottoms = set([(11, 15), (11, 14), (12, 15), (12, 14), (12, 13), (13, 15), (13, 14), (13, 13), (13, 12), (14, 15), (14, 14), (14, 13), (14, 12), (14, 11), (15, 15), (15, 14), (15, 13), (15, 12), (15, 11)])
        
        self.scoreBoard4w = [[-2,-1,0,1,2,7,9,11,13,15,17,19,21,23,25,27],[-1,1,2,3,4,7,9,11,13,15,17,19,21,23,25,27],[0,2,4,5,6,7,9,11,13,15,17,19,21,23,25,27],[1,3,5,6,7,8,9,11,13,15,17,19,21,23,25,27],[2,4,6,7,8,9,10,11,13,15,17,19,21,23,25,27],[7,7,7,8,9,10,11,12,13,15,17,19,21,23,25,27],[9,9,9,9,10,11,12,13,14,15,17,19,21,23,25,27],[11,11,11,11,11,12,13,14,15,16,17,19,21,23,25,27],[13,13,13,13,13,13,14,15,16,17,18,19,21,23,25,27],[15,15,15,15,15,15,15,16,17,18,19,20,21,23,25,27],[17,17,17,17,17,17,17,17,18,19,20,21,22,23,25,27],[19,19,19,19,19,19,19,19,19,20,21,22,23,24,25,27],[21,21,21,21,21,21,21,21,21,21,22,23,24,25,26,27],[23,23,23,23,23,23,23,23,23,23,23,24,25,26,27,28],[25,25,25,25,25,25,25,25,25,25,25,25,26,27,28,29],[27,27,27,27,27,27,27,27,27,27,27,27,27,28,29,30]]


        self.scoreBoard4b = []
        for line in self.scoreBoard4w[::-1]:
            self.scoreBoard4b.append(line[::-1])
        self.endTime = math.inf
        self.forbiddenMoves = dict()
        self.runPhase = False
        
    def readInput(self, io):
        global datafilename
        self.isSingleMode = io.rdSingle(str).startswith('SINGLE')
        self.isWhite = io.rdSingle(str).startswith('WHITE')
        self.isWhiteInt = self.isWhite * 2 - 1
        self.timeLeft = io.rdSingle(float)
        self.board = io.rdMat(lambda s: 1 if s == 'W' else (2 if s == 'B' else 0), 16)
        self.whites = set((i, j) for i in range(16) for j in range(16) if self.board[i][j] == 1)
        self.blacks = set((i, j) for i in range(16) for j in range(16) if self.board[i][j] == 2)
        self.selfCamp = self.rightbottoms if self.isWhite else self.lefttops
        self.oppoCamp = self.lefttops if self.lefttops else self.rightbottoms
        self.curScore = self.judgebd()
        self.needMinLayer = self.checkBWRangeOverlap()
        self.timefactor = 1.0
        self.abhold = 0
        self.depth = 4
        self.finalPath = None
        self.finalScore = -math.inf
        self.curMoves = []
        if DEBUG:
            datafilename = ("_W" if self.isWhite else "_B") + datafilename
        return self
    def writeOutput(self, io):
        io.wtRes(self.res)

    def checkBWRangeOverlap(self):
        whiteRan = [math.inf, -math.inf]
        blackRan = [math.inf, -math.inf]
        for i, j in self.whites:
            d = i + j
            whiteRan[0] = min(whiteRan[0], d)
            whiteRan[1] = max(whiteRan[1], d) 
        for i, j in self.blacks:
            d = i + j
            blackRan[0] = min(blackRan[0], d)
            blackRan[1] = max(blackRan[1], d)
        return blackRan[0] < whiteRan[1] and blackRan[1] > whiteRan[0]
    def getbd(self, pos):
        return self.board[pos[0]][pos[1]]
    def setbd(self, pos, v):
        if self.board[pos[0]][pos[1]] == v: return
        if self.board[pos[0]][pos[1]] == 1:
            self.whites.remove(pos)
        elif self.board[pos[0]][pos[1]] == 2:
            self.blacks.remove(pos)
        self.board[pos[0]][pos[1]] = v
        if v == 1:
            self.whites.add(pos)
        elif v == 2:
            self.blacks.add(pos)
    def movebd(self, p1, p2):
        self.setbd(p2, self.getbd(p1))
        self.setbd(p1, 0)
    def isvalid(self, pos):
        return pos[0] >= 0 and pos[0] < 16 and pos[1] >= 0 and pos[1] < 16

    def judgebd(self):
        s = 0
        sign = (1 if self.isWhite else -1)
        for i, j in self.whites:
            s += -self.scoreBoard4w[i][j]
        for i, j in self.blacks:
            s += self.scoreBoard4b[i][j]
        return s * sign
    def isfinished(self):
        occupied = False
        if self.isWhite:
            for pos in self.lefttops:
                if self.getbd(pos) == 0:
                    return False
                if self.getbd(pos) == 1:
                    occupied = True
        else:
            for pos in self.rightbottoms:
                if self.getbd(pos) == 0:
                    return False
                if self.getbd(pos) == 2:
                    occupied = True
        return occupied
    def further(self, possrc, posdes):
        ds = possrc[0] + possrc[1]
        dd = posdes[0] + posdes[1]
        return (ds - dd) * self.isWhiteInt
    def clearOfCamps(self):
        if self.isWhite:
            for pos in self.rightbottoms:
                if self.getbd(pos) == 1:
                    return False
        else:
            for pos in self.lefttops:
                if self.getbd(pos) == 2:
                    return False
        return True
    
    explorePcCalled = 0
    def explorePc(self, visited, pos, onlyouter, forwrite):
        self.explorePcCalled += 1
        edirs = self.edirs4w if forwrite else self.edirs4b
        jdirs = map(lambda d: (d[0] * 2, d[1] * 2), edirs)
        # Explore E
        if not onlyouter:
            for dir in edirs:
                npos = TupleOp.addt(pos, dir)
                if not self.isvalid(npos):
                    continue
                if self.getbd(npos) == 0:
                    yield 'E', npos
        # Explore J
        yield 'J', [pos]
        for idir, odir in zip(edirs, jdirs):
            nipos = TupleOp.addt(pos, idir)
            nopos = TupleOp.addt(pos, odir)
            if not self.isvalid(nopos):
                continue
            if self.getbd(nipos) == 0 or self.getbd(nopos) != 0:
                continue
            if nopos in visited:
                continue
            visited.add(nopos)
            # Cannot move out if in the target camp
            if forwrite and pos in self.lefttops and not nopos in self.lefttops or (not forwrite and pos in self.rightbottoms and not nopos in self.rightbottoms):
                continue
            # Cannot move back (the back move is stored in forbiddenMoves)
            # if pos in self.forbiddenMoves and nopos in self.forbiddenMoves[pos]:
            #     continue
            for _, path in self.explorePc(visited, nopos, True, forwrite):
                path.append(pos)
                yield 'J', path

    exploreBnCalled = 0
    curBnDepth = 0
    def exploreBn(self, iswhite, usemove, depth, alpha, beta, validScore):
        if not (DEBUG and IGNORETIME):
            if time.time() > self.endTime and not usemove:
                debug("Time out !!")
                raise GameTimeoutError(None)

        self.exploreBnCalled += 1
        isfinished = self.isfinished()
        if depth == 0 or isfinished:
            jgres = self.judgebd() + validScore
            if isfinished:
                jgres += depth # If found the path to end, we need shortest path
                if jgres > self.finalScore:
                    self.finalPath = copy.copy(self.curMoves)
            return (jgres, [])

        maxplayer = (iswhite == self.isWhite)
        posset = list(self.whites if iswhite else self.blacks)
        if iswhite:
            posset.sort(key=lambda p: -p[0] - p[1])
        else:
            posset.sort(key=lambda p: p[0] + p[1])

        if maxplayer:
            score = (-math.inf, [])
        else:
            score = (math.inf, [])
        for pos in posset:
            visitedposs = set()
            for pathType, path in self.explorePc(visitedposs, pos, False, iswhite):
                if pathType == 'E':
                    movePath = [Move('E', pos, path)]
                else:
                    if len(path) < 2: continue
                    movePath = [Move('J', ps, pe) for ps, pe in zip(path[-1::-1], path[-2::-1])]
                st, ed = movePath[0].st, movePath[-1].ed
                # Check if the path cause valid start move, if so add validScore
                if usemove:
                    validScore = 0
                    if st in self.selfCamp and not ed in self.selfCamp:
                        validScore = 80
                    elif st in self.selfCamp and ed in self.selfCamp:
                        dist = self.further(st, ed)
                        if dist > 0:
                            validScore = dist * 10
                
                # Modify board to enter recursion
                self.movebd(st, ed)
                self.curMoves.append(movePath)
                self.curBnDepth += 1
                try:
                    jgres, nextPaths = None, []
                    if self.needMinLayer:
                        jgres, nextPaths = self.exploreBn(not iswhite, False, depth - 1, alpha, beta, validScore)
                    else:
                        nscore = self.judgebd()
                        if nscore >= self.curScore:
                            jgres, nextPaths = self.exploreBn(iswhite, False, depth - 1, alpha, beta, validScore)
                except GameTimeoutError:
                    if not usemove:
                        raise GameTimeoutError(None)
                    else:
                        return score if score[1] is not None else (-math.inf, movePath)
                finally:
                    self.curMoves.pop()
                    self.movebd(ed, st)
                    self.curBnDepth -= 1
                # Restore board to end recursion

                if jgres is None: continue
                nextPaths.append(movePath)
                if maxplayer:
                    score = score if score[0] >= jgres else (jgres, nextPaths)
                    if alpha < score[0]:
                        alpha = score[0]
                else:
                    score = score if score[0] <= jgres else (jgres, nextPaths)
                    beta = beta if beta <= score[0] else score[0]
                if alpha >= beta - self.abhold: break
            if alpha >= beta - self.abhold: break
        return score

    def do(self):
        pathRecord = IO.rdObjIfValid()
        if self.clearOfCamps() and pathRecord is not None:
            if self.validateRecordedPath(pathRecord[0]):
                self.res = pathRecord[0]
                IO.wtObj(pathRecord[1:])
                debug('Applied saved path')
                return
            IO.rmObjFile()
            debug('Validation failed, Data file removed')
        
        estComplex = self.estimateComplexity()
        debug('estimated complex:', estComplex)
        if self.isSingleMode:
            roundTime = self.timeLeft
        else:
            roundTime = 1.0
        depth = self.estimateDepth(roundTime, estComplex)
        self.endTime = roundTime + startTime
        if self.timeLeft < 0.05: self.endTime = 0.05
        if not self.needMinLayer: depth = (depth + 1) // 2
        if self.isSingleMode: depth = 1
        debug('estimated depth:', depth, "isSingle:", self.isSingleMode, "needMinLayer:", self.needMinLayer)


        # depth = 3
        # self.needMinLayer = True
        # self.abhold = 1

        self.runPhase = True
        tst = time.time()
        score = self.exploreBn(self.isWhite, True, depth, -math.inf, math.inf, 0)
        score[1].reverse()
        bestPaths = score[1]
        if self.needMinLayer:
            bestPaths = bestPaths[::2]
        ted = time.time()

        debug('time: ', ted - tst)
        debug('score', score[0])
        for path in bestPaths:
            debug(' path', path)
        debug('bn', self.exploreBnCalled)
        debug('pc', self.explorePcCalled)
        # if self.finalPath is not None:
        #     IO.wtObj(self.finalPath[1:])
        #     debug('Saved final path')
        pathsToSave = bestPaths[1:]
        IO.wtObj(pathsToSave)
        debug('Saved paths #:', len(pathsToSave))
        
        self.res = bestPaths[0]

    def validateRecordedPath(self, moves):
        lasted = None
        for i, move in enumerate(moves):
            if move.mtype == 'E':
                if len(moves) > 1:
                    return False
                if (not self.getbd(move.st) == 1 and self.isWhite): return False
                if (not self.getbd(move.st) == 2 and not self.isWhite): return False
                if self.getbd(move.ed) != 0: return False
            else:
                if i == 0:
                    if (not self.getbd(move.st) == 1 and self.isWhite): return False
                    if (not self.getbd(move.st) == 2 and not self.isWhite): return False
                else:
                    if lasted != move.st: return False
                if self.getbd(move.ed) != 0: return False
                lasted = move.ed
        return True

    def estimateComplexity(self):
        self.exploreBn(self.isWhite, True, 1, -math.inf, math.inf, 0)
        v = self.exploreBnCalled
        self.exploreBnCalled, self.explorePcCalled = 0, 0
        return v

    def estimateDepth(self, roundTime, estComplexity):
        if estComplexity < 10:
            return 3
        d = math.log(roundTime / (self.timefactor * fixedTimeC), estComplexity)
        dd = math.floor(d)
        return dd if dd > 0 else 1

    def __repr__(self):
        return "%s %s timeleft: %s" % ("Single" if self.isSingleMode else "Game", "White" if self.isWhite else "Black", self.timeLeft)
    def dumpbd(self):
        mio = IO('dumpinput.txt', 'w')
        mio.wtLine(['SINGLE' if self.isSingleMode else 'GAME'], ' ')
        mio.wtLine(['WHITE' if self.isWhite else 'BLACK'], ' ')
        mio.wtLine([str(self.timeLeft)], ' ')
        for line in self.board:
            mio.wtLine(map(lambda i: 'W' if i == 1 else ('B' if i == 2 else "."), line), '')
        mio.close()
    def applyAndDump(self, st, ed):
        self.movebd(st, ed)
        self.dumpbd()
        self.movebd(ed, st)
    
if len(sys.argv) > 1 and sys.argv[1] == 'showdata':
    with open(sys.argv[2], "rb") as f:
        obj = pickle.load(f)
        print(obj)
    exit()

inputIO = IO('input.txt', 'r')
sol = Solution()
sol.readInput(inputIO)
print(sol)
inputIO.close()

sol.do()

outIO = IO('output.txt', 'w')
sol.writeOutput(outIO)
outIO.close()
