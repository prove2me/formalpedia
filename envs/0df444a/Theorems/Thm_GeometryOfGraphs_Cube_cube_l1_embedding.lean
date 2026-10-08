-- Prove2me | Theorems.Thm_GeometryOfGraphs_Cube_cube_l1_embedding
-- name    : GeometryOfGraphs.Cube.cube_l1_embedding
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:39:33.929478+00:00
-- url     : https://prove2.me/theorems/f0bdedaf-30fc-4540-a3f8-2deeb3eeab03
-- title:
--   Proof of Corollary 5.12 — cube embeds in ℓ₁ to dimension m
-- statement:
--   For every $m\geq0$, the $m$-cube embeds isometrically in $\ell_1^m$: there is a coordinate map $\varphi$ such that for every pair of cube vertices $x,y$,
--
--   $$
--   \sum_{k=1}^{m}|\varphi(x)_k-\varphi(y)_k|=d_{m\text{-Cube}}(x,y).
--   $$
--
--   This is the upper-bound assertion in the proof of Corollary 5.12. The zero-dimensional instance is a single vertex.
-- source:
--   N. Linial, E. London, Y. Rabinovich, The geometry of graphs and some of its algorithmic applications, Combinatorica 15 (1995), p. 233, proof of Corollary 5.12, first sentence; https://doi.org/10.1007/BF01200757

import Definitions.Def_GeometryOfGraphs_Cube_Hypercube

set_option autoImplicit false

namespace GeometryOfGraphs.Cube

/-- The cube embeds isometrically in `ℓ₁^m`. -/
theorem cube_l1_embedding (m : ℕ) :
    ∃ φ : (Fin m → Bool) → (Fin m → ℝ), ∀ x y,
      (∑ k : Fin m, |φ x k - φ y k|) = ((hypercube m).dist x y : ℝ) := by sorry

end GeometryOfGraphs.Cube
