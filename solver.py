import sys
from threading import Event
from utils import SATSolverResult, load_formula, lit_to_dimacs
import random


class Solver:
    def __init__(self, filename: str, sigkill: Event):
        self.sigkill = sigkill
        self.formula = load_formula(filename)
        self.num_vars = self.formula.num_vars
        num_lits = self.formula.num_lits

        # Присваивание: values[ℓ] = 1 (истинен), -1 (ложен), 0 (не означен).
        # Хранится и для ℓ, и для ¬ℓ: values[ℓ] == -values[ℓ ^ 1].
        self.values = [0] * num_lits

        # Трейл — означенные литералы в порядке присваивания.
        # trail[:propagated] уже распространены, trail[propagated:] — ещё нет.
        self.trail = []
        self.propagated = 0

        # control[i] — позиция в trail решения уровня i + 1;
        # текущий уровень решения = len(control).
        self.control = []

        self.model = None

        self.preprocess()

    def preprocess(self):
        """
        Разбор дизъюнктов формулы:
          clauses          — дизъюнкты длины ≥ 2, без повторов литералов и тавтологий (a ∨ ¬a ∨ ...)
          units            — литералы единичных дизъюнктов
          has_empty_clause — во входе есть пустой дизъюнкт (формула невыполнима)
        """
        self.clauses = []
        self.units = []
        self.has_empty_clause = False
        for clause in self.formula.clauses:
            lits = set(clause)
            if not lits:
                self.has_empty_clause = True
            elif any(lit ^ 1 in lits for lit in lits):
                continue
            elif len(lits) == 1:
                self.units.append(lits.pop())
            else:
                self.clauses.append(list(lits))

    def level(self) -> int:
        return len(self.control)

    def assign(self, lit: int):
        """Сделать ℓ истинным на текущем уровне."""
        self.values[lit] = 1
        self.values[lit ^ 1] = -1
        self.trail.append(lit)

    def decide(self, lit: int):
        """Открыть новый уровень решения и сделать ℓ истинным."""
        self.control.append(len(self.trail))
        self.assign(lit)

    def decision(self, level: int) -> int:
        """Литерал-решение уровня level (1 ≤ level ≤ self.level())."""
        return self.trail[self.control[level - 1]]

    def backtrack(self, level: int):
        """Отменить все присваивания уровней > level."""
        if level >= len(self.control):
            return
        values, trail = self.values, self.trail
        start = self.control[level]
        for i in range(start, len(trail)):
            lit = trail[i]
            values[lit] = 0
            values[lit ^ 1] = 0
        del trail[start:]
        del self.control[level:]
        self.propagated = start

    def save_model(self):
        values = self.values
        self.model = [lit_to_dimacs(2 * v if values[2 * v] > 0 else 2 * v + 1)
                      for v in range(1, self.num_vars + 1)]

    def build_occurrences(self):
        self.occurrences = [[] for _ in range(self.formula.num_lits)]
        for c in self.clauses:
            for lit in c:
                self.occurrences[lit].append(c)

    def build_watches(self):
        num_lits = self.formula.num_lits
        self.binary = [[] for _ in range(num_lits)]
        self.watches = [[] for _ in range(num_lits)]
        for c in self.clauses:
            if len(c) == 2:
                self.binary[c[0]].append(c[1])
                self.binary[c[1]].append(c[0])
            else:
                self.watches[c[0]].append([c[1], c])
                self.watches[c[1]].append([c[0], c])

    def propagate(self) -> bool:
        """
        UnitPropagate: распространить литералы trail[propagated:].
        Возвращает True, если найден конфликт (все литералы дизъюнкта ложны).
        """
        while self.propagated < len(self.trail):
            lit = self.trail[self.propagated] ^ 1
            for l in self.binary[lit]:
                if self.values[l] == 1:
                    continue
                if self.values[l] == -1:
                    return True
                else:
                    self.assign(l)

            ws = self.watches[lit]
            i = 0
            while i < len(ws):
                c1, c = ws[i]
                if c[0] == lit:
                    c[0], c[1] = c[1], c[0]
                c1 = c[0]
                ws[i][0] = c1
                if self.values[c1] == 1:
                    i += 1
                    continue

                new_ix = None
                for ix in range(2, len(c)):
                    if self.values[c[ix]] != -1:
                        new_ix = ix
                        break

                if new_ix is not None:
                    x = c[new_ix]
                    c[1], c[new_ix] = x, lit
                    self.watches[x].append([c1, c])

                    ws[i] = ws[-1]
                    ws.pop()
                    continue

                if self.values[c1] == -1:
                    return True
                self.assign(c1)
                i += 1
            self.propagated += 1
        return False

    def choose_literal(self):
        """
        ChooseLiteral: литерал для следующего решения или None, если все
        переменные означены.
        """
        # maybe random?
        for i in range(2, len(self.values), 2):
            if self.values[i] == 0:
                return i
        return None


    def solve(self) -> SATSolverResult:
        self.build_watches()
        if self.has_empty_clause:
            return SATSolverResult.UNSAT
        for lit in self.units:
            if self.values[lit] == -1:
                return SATSolverResult.UNSAT
            if self.values[lit] == 0:
                self.assign(lit)
        iters_count = 0
        while True:
            iters_count += 1
            if iters_count % 10_000 == 0 and self.sigkill.is_set():
                return SATSolverResult.UNKNOWN
            while self.propagate():
                lvl = self.level()
                if lvl == 0:
                    return SATSolverResult.UNSAT
                lit = self.decision(lvl)
                self.backtrack(lvl - 1)
                self.assign(lit ^ 1)
                continue
            lit = self.choose_literal()
            if lit is None:
                break
            self.decide(lit)
        return SATSolverResult.SAT

if __name__ == "__main__":
    result = Solver(sys.argv[1], Event()).solve()
    if result == SATSolverResult.SAT:
        print("sat")
    elif result == SATSolverResult.UNSAT:
        print("unsat")
    else:
        print("unknown")
