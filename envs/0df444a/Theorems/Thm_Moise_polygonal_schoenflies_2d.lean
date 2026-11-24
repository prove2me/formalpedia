-- Prove2me | Theorems.Thm_Moise_polygonal_schoenflies_2d
-- name    : Moise.polygonal_schoenflies_2d
-- status  : Open
-- author  : @wojtek_politarczyk
-- created : 2026-11-24T19:55:00.622688+00:00
-- url     : https://prove2.me/theorems/b918e96a-dbc4-477a-9feb-e8375514070e
-- title:
--   Schoenflies theorem for polygons
-- statement:
--   Let $P$ be a finite $1$-dimensional Euclidean complex in $\mathbb{R}^2$ whose polyhedron $|P|$ is homeomorphic to $S^1$ (a simple closed polygon), and let $\Delta^2 = \operatorname{conv}\{(0,0), (1,0), (0,1)\}$ be the standard $2$-simplex in $\mathbb{R}^2$. Then there exists a piecewise-linear homeomorphism $f : \mathbb{R}^2 \to \mathbb{R}^2$ (with respect to Euclidean complexes $K_1, K_2$ triangulating $\mathbb{R}^2$) mapping $|P|$ onto the boundary of $\Delta^2$:
--
--   $$f(|P|) = \partial \Delta^2.$$
-- source:
--   E. E. Moise, Geometric Topology in Dimensions 2 and 3, Springer GTM 47, 1977, Chapter 3.

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Convex.Hull
import Definitions.Def_Moise_EuclideanComplex

namespace Moise

theorem polygonal_schoenflies_2d (P : EuclideanComplex 2)
    (hfin : P.IsFinite) (hdim : ∀ σ ∈ P.simplices, σ.dim ≤ 1)
    (hS1 : Nonempty (P.polyhedron ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1)) :
    ∃ (K₁ K₂ : EuclideanComplex 2),
      K₁.polyhedron = Set.univ ∧ K₂.polyhedron = Set.univ ∧
      ∃ f : K₁.polyhedron ≃ₜ K₂.polyhedron,
        IsPLHomeomorph K₁ K₂ f ∧
        Subtype.val '' (f '' (Subtype.val ⁻¹' P.polyhedron)) =
          frontier (convexHull ℝ
            ({(0 : EuclideanSpace ℝ (Fin 2)),
              (WithLp.equiv 2 (Fin 2 → ℝ)).symm ![1, 0],
              (WithLp.equiv 2 (Fin 2 → ℝ)).symm ![0, 1]} : Set (EuclideanSpace ℝ (Fin 2)))) := by sorry

end Moise
