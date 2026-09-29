-- Prove2me | Theorems.Thm_LinearOptimization_convex_hull_finite_is_polyhedron
-- name    : LinearOptimization.convex_hull_finite_is_polyhedron
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-05T01:18:49.42369+00:00
-- url     : https://prove2.me/theorems/e4c9d835-cada-4b10-bbcc-45616a3d41d1
-- title:
--   The convex hull of finitely many vectors is a polyhedron
-- statement:
--   **(Corollary 2.6)** The convex hull of a finite number of vectors is a polyhedron.
--
--   (Proof route: the convex hull
--
--   $$\{\sum_{i=1}^k \lambda_i x^i \mid \lambda_i \ge 0,\ \sum_{i=1}^k \lambda_i = 1\}$$
--
--   of $x^1, \dots, x^k$ is the image of the polyhedron $\{\lambda \in \mathbb{R}^k \mid \lambda \ge 0,\ \sum_i \lambda_i = 1\}$ under the linear mapping $(\lambda_1, \dots, \lambda_k) \mapsto \sum_{i=1}^k \lambda_i x^i$.)
-- source:
--   Bertsimas & Tsitsiklis, Introduction to Linear Optimization, Athena Scientific, 1997, Corollary 2.6, p. 74

import Mathlib.Analysis.Convex.Hull
import Definitions.Def_Polyhedron


/-- **Bertsimas & Tsitsiklis, Corollary 2.6 (p. 74).** The convex hull of finitely many vectors
in `ℝⁿ` admits a general-form polyhedral presentation. -/

theorem LinearOptimization.convex_hull_finite_is_polyhedron {n k : ℕ}
    (v : Fin k → (Fin n → ℝ)) :
    ∃ (m' : ℕ) (A' : Matrix (Fin m') (Fin n) ℝ) (b' : Fin m' → ℝ),
      convexHull ℝ (Set.range v) = polyhedron A' b' := by
  sorry
