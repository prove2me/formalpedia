-- Prove2me | Theorems.Thm_LinearOptimization_simplex_termination_nondegenerate
-- name    : LinearOptimization.simplex_termination_nondegenerate
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-05T17:24:06.831206+00:00
-- url     : https://prove2.me/theorems/a0d5585c-0a1b-46be-9836-ff8935ea14fb
-- title:
--   Finite termination of the simplex method under nondegeneracy
-- statement:
--   **(Theorem 3.3, GOAL)** Assume that the feasible set is nonempty and that every basic feasible solution is nondegenerate. Then, the simplex method terminates after a finite number of iterations. At termination, there are the following two possibilities:
--
--   - **(a)** we have an optimal basis $B$ and an associated basic feasible solution which is optimal;
--   - **(b)** we have found a vector $d$ satisfying $Ad = 0$, $d \ge 0$, and $c'd < 0$, and the optimal cost is $-\infty$.
--
--   *Encoding:* (Termination is encoded as: there is no infinite admissible pivot run, and every maximal run ends in one of the two terminal states.)
-- source:
--   Bertsimas & Tsitsiklis, Introduction to Linear Optimization, Athena Scientific, 1997, Theorem 3.3, p. 91

import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Definitions.Def_LinearOptimization_SimplexPivot
import Definitions.Def_LinearOptimization_OptimalBasis


open Matrix

/-- **Bertsimas & Tsitsiklis, Theorem 3.3 (p. 91).** Termination of the simplex method under
nondegeneracy: if the standard-form feasible set is nonempty and every
basic feasible solution is nondegenerate, then no infinite pivot run
exists, and every admissible state admitting no further pivot exhibits
either an optimal basis with an optimal associated basic feasible
solution, or a direction `d` with `Ad = 0`, `d ≥ 0`, `c'd < 0`
certifying optimal cost `−∞`. -/

theorem LinearOptimization.simplex_termination_nondegenerate {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (hA : LinearIndependent ℝ (fun i => A i))
    (hne : (stdPolyhedron A b).Nonempty)
    (hnd : ∀ x, IsBasicFeasibleSolution (stdFormSystem A b) x →
      ¬IsStdDegenerateBasicSolution A b x) :
    (¬∃ f : ℕ → (Fin m ↪ Fin n) × (Fin n → ℝ),
      (∀ k, IsSimplexState A b (f k).1 (f k).2) ∧
      ∀ k, IsSimplexPivot A c (f k).1 (f k).2 (f (k + 1)).1 (f (k + 1)).2) ∧
    ∀ (B : Fin m ↪ Fin n) (x : Fin n → ℝ), IsSimplexState A b B x →
      (¬∃ (B' : Fin m ↪ Fin n) (x' : Fin n → ℝ), IsSimplexPivot A c B x B' x') →
      (IsOptimalBasis A b c B ∧ IsLpOptimal c (stdPolyhedron A b) x) ∨
      ∃ d : Fin n → ℝ, A.mulVec d = 0 ∧ 0 ≤ d ∧ c ⬝ᵥ d < 0 ∧
        lpValue c (stdPolyhedron A b) = ⊥ := by
  sorry
