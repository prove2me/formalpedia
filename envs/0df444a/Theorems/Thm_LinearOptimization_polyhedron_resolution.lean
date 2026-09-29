-- Prove2me | Theorems.Thm_LinearOptimization_polyhedron_resolution
-- name    : LinearOptimization.polyhedron_resolution
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-05T20:48:41.560521+00:00
-- url     : https://prove2.me/theorems/c8b54696-f271-4510-80af-91dff50c2be7
-- title:
--   Resolution theorem for polyhedra
-- statement:
--   **(Theorem 4.15, resolution theorem — GOAL)** Let $P = \{x \in \mathbb{R}^n \mid Ax \ge b\}$ be a nonempty polyhedron with at least one extreme point. Let $x^1, \dots, x^k$ be the extreme points, and let $w^1, \dots, w^r$ be a complete set of extreme rays of $P$. Let
--
--   $$Q = \left\{\sum_{i=1}^{k} \lambda_i x^i + \sum_{j=1}^{r} \theta_j w^j \;\middle|\; \lambda_i \ge 0,\ \theta_j \ge 0,\ \sum_{i=1}^{k} \lambda_i = 1\right\}.$$
--
--   Then, $Q = P$.
-- source:
--   Bertsimas & Tsitsiklis, Introduction to Linear Optimization, Athena Scientific, 1997, Theorem 4.15, p. 179

import Mathlib.Analysis.Convex.Extreme
import Definitions.Def_LinearOptimization_RecessionCone
import Definitions.Def_LinearOptimization_FinitelyGeneratedSet


open Matrix

/-- **Bertsimas & Tsitsiklis, Theorem 4.15 (p. 179).** Resolution theorem: a nonempty
polyhedron `P = {x | Ax ≥ b}` with at least one extreme point equals the
finitely generated set built from its extreme points and any complete set
of its extreme rays. -/

theorem LinearOptimization.polyhedron_resolution {m n k r : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (hne : (polyhedron A b).Nonempty)
    (x : Fin k → (Fin n → ℝ)) (hk : 0 < k)
    (hx : Set.extremePoints ℝ (polyhedron A b) = Set.range x)
    (w : Fin r → (Fin n → ℝ)) (hw : IsCompleteExtremeRaySet A w) :
    finitelyGeneratedSet x w = polyhedron A b := by
  sorry
