-- Prove2me | Theorems.Thm_LinearOptimization_lp_optimal_cost_concave_in_cost
-- name    : LinearOptimization.lp_optimal_cost_concave_in_cost
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-05T21:06:34.993198+00:00
-- url     : https://prove2.me/theorems/9bcbcb34-7c44-4dc7-b171-7adb778939c0
-- title:
--   Concavity of the optimal cost in the cost vector $c$
-- statement:
--   **(Theorem 5.3, p. 217)** Consider a feasible linear programming problem in standard form.
--
--   - **(a)** The set $T$ of all $c$ for which the optimal cost is finite, is convex.
--   - **(b)** The optimal cost $G(c)$ is a concave function of $c$ on the set $T$.
--   - **(c)** If for some value of $c$ the primal problem has a unique optimal solution $x^*$, then $G$ is linear in the vicinity of $c$ and its gradient is equal to $x^*$.
-- source:
--   Bertsimas & Tsitsiklis, Introduction to Linear Optimization, Athena Scientific, 1997, Theorem 5.3, p. 217

import Mathlib.Analysis.Convex.Function
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Definitions.Def_LinearOptimization_OptimalCostFunction


open Matrix

/-- **Bertsimas & Tsitsiklis, Theorem 5.3 (p. 217).** For a feasible standard form problem
(rows of `A` linearly independent): (a) the set `T` of cost vectors with
finite optimal cost is convex; (b) the optimal cost `G(c)` is concave on
`T`; (c) if the primal has a unique optimal solution `x*` for the cost
vector `c`, then `G` is linear in a vicinity of `c` with gradient `x*`. -/

theorem LinearOptimization.lp_optimal_cost_concave_in_cost {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (G : (Fin n → ℝ) → ℝ)
    (hrank : LinearIndependent ℝ (fun i => A i))
    (hfeas : (stdPolyhedron A b).Nonempty)
    (hG : ∀ c ∈ finiteCostSet A b, ((G c : ℝ) : EReal) = lpOptimalCostCost A b c) :
    Convex ℝ (finiteCostSet A b) ∧
    ConcaveOn ℝ (finiteCostSet A b) G ∧
    ∀ (c xstar : Fin n → ℝ),
      IsLpOptimal c (stdPolyhedron A b) xstar →
      (∀ y, IsLpOptimal c (stdPolyhedron A b) y → y = xstar) →
      ∃ ε > (0 : ℝ), ∀ c' : Fin n → ℝ, (∀ j, |c' j - c j| < ε) →
        c' ∈ finiteCostSet A b ∧ G c' = G c + (c' - c) ⬝ᵥ xstar := by
  sorry
