-- Prove2me | Theorems.Thm_LinearOptimization_lp_dual_optimal_iff_subgradient
-- name    : LinearOptimization.lp_dual_optimal_iff_subgradient
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-05T21:06:20.177675+00:00
-- url     : https://prove2.me/theorems/e6f35c44-65b7-4baa-b4d5-c51335e16393
-- title:
--   Dual optimal solutions are exactly the subgradients of the optimal cost function
-- statement:
--   **(Theorem 5.2, p. 216 — GOAL)** Suppose that the linear programming problem of minimizing $c'x$ subject to $Ax = b^*$ and $x \ge 0$ is feasible and that the optimal cost is finite.
--
--   Then, a vector $p$ is an optimal solution to the dual problem if and only if it is a subgradient of the optimal cost function $F$ at the point $b^*$.
-- source:
--   Bertsimas & Tsitsiklis, Introduction to Linear Optimization, Athena Scientific, 1997, Theorem 5.2, p. 216

import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Definitions.Def_LinearOptimization_OptimalCostFunction
import Definitions.Def_LinearOptimization_Subgradient


open Matrix

/-- **Bertsimas & Tsitsiklis, Theorem 5.2 (p. 216).** For a standard form problem feasible at
`b*` with finite optimal cost (rows of `A` linearly independent), `p` is
an optimal solution of the dual `max p'b*, p'A ≤ c'` if and only if `p`
is a subgradient of the optimal cost function `F` at `b*` relative to the
set `S` of feasible right-hand sides. -/

theorem LinearOptimization.lp_dual_optimal_iff_subgradient {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ) (bstar : Fin m → ℝ)
    (F : (Fin m → ℝ) → ℝ) (p : Fin m → ℝ)
    (hrank : LinearIndependent ℝ (fun i => A i))
    (hfeas : (stdPolyhedron A bstar).Nonempty)
    (hfin : lpOptimalCostRhs A c bstar ≠ ⊥)
    (hF : ∀ b ∈ feasibleRhsSet A, ((F b : ℝ) : EReal) = lpOptimalCostRhs A c b) :
    IsLpDualOptimal bstar (dualFeasibleStd A c) p ↔
      IsSubgradientOn F (feasibleRhsSet A) p bstar := by
  sorry
