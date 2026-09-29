-- Prove2me | Theorems.Thm_LinearOptimization_lp_unbounded_iff_extreme_ray
-- name    : LinearOptimization.lp_unbounded_iff_extreme_ray
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-05T20:48:18.859906+00:00
-- url     : https://prove2.me/theorems/da74cb19-d6c7-431c-9ee4-44a7561920a0
-- title:
--   Unboundedness of a linear program via extreme rays of the feasible set
-- statement:
--   **(Theorem 4.14)** Consider the problem of minimizing $c'x$ subject to $Ax \ge b$, and assume that the feasible set has at least one extreme point.
--
--   The optimal cost is equal to $-\infty$ if and only if some extreme ray $d$ of the feasible set satisfies $c'd < 0$.
--
--   (Interestingly, this criterion does not involve the right-hand side vector $b$.)
-- source:
--   Bertsimas & Tsitsiklis, Introduction to Linear Optimization, Athena Scientific, 1997, Theorem 4.14, p. 178

import Mathlib.Analysis.Convex.Extreme
import Definitions.Def_LinearOptimization_RecessionCone


open Matrix

/-- **Bertsimas & Tsitsiklis, Theorem 4.14 (p. 178).** For `min c'x` over `{x | Ax ≥ b}` with
at least one extreme point: the optimal cost is `−∞` iff some extreme ray
`d` of the feasible set satisfies `c'd < 0`. -/

theorem LinearOptimization.lp_unbounded_iff_extreme_ray {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (hext : (Set.extremePoints ℝ (polyhedron A b)).Nonempty) :
    lpValue c (polyhedron A b) = ⊥ ↔
      ∃ d : Fin n → ℝ, IsExtremeRay A d ∧ c ⬝ᵥ d < 0 := by
  sorry
