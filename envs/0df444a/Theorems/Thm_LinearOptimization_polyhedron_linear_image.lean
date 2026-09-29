-- Prove2me | Theorems.Thm_LinearOptimization_polyhedron_linear_image
-- name    : LinearOptimization.polyhedron_linear_image
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-05T01:18:41.990458+00:00
-- url     : https://prove2.me/theorems/39d445f1-e8f7-4cfd-af28-af7d117e1a7f
-- title:
--   Linear images of polyhedra are polyhedra
-- statement:
--   **(Corollary 2.5)** Let $P \subset \mathbb{R}^n$ be a polyhedron and let $A$ be an $m \times n$ matrix. Then, the set
--
--   $$Q = \{Ax \mid x \in P\}$$
--
--   is also a polyhedron.
-- source:
--   Bertsimas & Tsitsiklis, Introduction to Linear Optimization, Athena Scientific, 1997, Corollary 2.5, p. 74

import Definitions.Def_Polyhedron


open Matrix

/-- **Bertsimas & Tsitsiklis, Corollary 2.5 (p. 74).** The image `{Mx | x ∈ P}` of a polyhedron
under a linear map (given by a matrix `M`) is a polyhedron. -/

theorem LinearOptimization.polyhedron_linear_image {m n p : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (M : Matrix (Fin p) (Fin n) ℝ) :
    ∃ (m' : ℕ) (A' : Matrix (Fin m') (Fin p) ℝ) (b' : Fin m' → ℝ),
      M.mulVec '' polyhedron A b = polyhedron A' b' := by
  sorry
