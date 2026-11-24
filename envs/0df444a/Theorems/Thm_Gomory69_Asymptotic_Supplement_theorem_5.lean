-- Prove2me | Theorems.Thm_Gomory69_Asymptotic_Supplement_theorem_5
-- name    : Gomory69.Asymptotic.Supplement.theorem_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T01:23:27.537026+00:00
-- url     : https://prove2.me/theorems/a7a62970-5942-49a0-8e49-d7fed497f131
-- title:
--   THEOREM 5 — A periodic selector of least-cost group optima
-- statement:
--   Fix the integer matrices $B,N$ and real costs $c$ of (2), with $\det B\ne0$, unit columns in $(B,N)$, and nonnegative relative prices $c_N^*=-c_N+c_BB^{-1}N$. Write $G=\mathbb Z^m/M(B)$, $f$ for the quotient map, $D=|\det B|$, and $l_{\max}$ for the largest Euclidean length of a column of $N$.
--
--   There is one selection $q\mapsto(x_N(q),t^*(q))$, defined on every quotient class, such that $t^*(fb)$ is a minimizing vertex of the group problem for every integer $b$, and $x_N(fb)$ is its corresponding least-cost-column lift. In particular,
--   $$x_N(f(b+B_i))=x_N(fb)\quad\text{for every integer }b\text{ and basis column }B_i.$$
--   For every integer $b\in K_B(l_{\max}(D-1))$, there is an integer $x_B$ such that
--   $$x_B=B^{-1}(b-Nx_N(fb)),\qquad (x_B,x_N(fb))\text{ is optimal for (2)}.$$
--   The aggregation $Fx^*=t^*$ and least-cost-column requirement are contained in the corresponding-lift predicate. The same selector is used everywhere; periodicity concerns selected vectors, not just feasible sets or objective values.
--
--   This is the periodic-solution companion to the published asymptotic optimality goal.
--
--   Differences from the source:
--   - reading: Theorem 5 uses the preceding optimal-basis and unit-matrix setting → nonsingular B, unit columns and nonnegative relative prices are explicit; reason: pp. 452, 460–462 supply these standing conditions; deep-cone membership supplies primal feasibility
--   - encoding: one periodic choice on equivalent integer right-hand sides → a function on quotient classes, evaluated at fb, with the column-period equality explicit; reason: the paragraph before Theorem 5 says the group equation is unchanged on each class
--   - reading: t* and x* are the choices constructed in the preceding theorems → the selected group optimum is a minimizing vertex and its lift is a corresponding vertex using least-cost columns; reason: p. 461 specifies these choices; their existence is concluded, not assumed
-- source:
--   Gomory, Some polyhedra related to combinatorial problems, Linear Algebra Appl. 2 (1969), DOI 10.1016/0024-3795(69)90017-2, p. 462, THEOREM 5

import Mathlib
import Definitions.Def_Gomory69_Asymptotic_IntegerProgram

namespace Gomory69.Asymptotic.Supplement

/-- One selector on quotient classes, hence periodic on the whole integer lattice. -/
theorem theorem_5 {m n : ℕ}
    (B : Matrix (Fin m) (Fin m) ℤ) (N : Matrix (Fin m) (Fin n) ℤ)
    (c : Fin m ⊕ Fin n → ℝ) (hB : B.det ≠ 0)
    (hunit : ContainsUnitMatrix B N) (hcost : ∀ i, 0 ≤ relativePrice B N c i) :
    ∃ (xN : FactorGroup B → Fin n → ℕ)
      (tstar : FactorGroup B → ↥(groupColumnSet B N) → ℝ),
      (∀ b : Fin m → ℤ,
        IsMinimizingVertex B N b c (tstar (toGroup B b)) ∧
        IsCorrespondingVertex B N c (tstar (toGroup B b)) (xN (toGroup B b))) ∧
      (∀ (b : Fin m → ℤ) (j : Fin m),
        xN (toGroup B (b + fun i => B i j)) = xN (toGroup B b)) ∧
      (∀ b : Fin m → ℤ,
        realVec b ∈ deepCone B (lmax N * ((detAbs B : ℝ) - 1)) →
        ∃ xB : Fin m → ℤ,
          (fun k => (xB k : ℝ)) = basicPart B N b (xN (toGroup B b)) ∧
          IsOptimal B N b c (Sum.elim xB (fun i => (xN (toGroup B b) i : ℤ)))) := by sorry

end Gomory69.Asymptotic.Supplement
