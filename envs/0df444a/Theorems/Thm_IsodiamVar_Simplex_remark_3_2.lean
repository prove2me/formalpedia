-- Prove2me | Theorems.Thm_IsodiamVar_Simplex_remark_3_2
-- name    : IsodiamVar.Simplex.remark_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:47:10.953884+00:00
-- url     : https://prove2.me/theorems/050b2655-ec8c-47c0-9aac-0b20d34a2bfb
-- title:
--   Remark 3.2 — barycenter determines uniform vertex mass
-- statement:
--   Let $x_0,\ldots,x_n$ be affinely independent points of $\mathbb R^n$, and let $\mu$ be a probability measure carried by these vertices. If its barycenter is their centroid, then
--
--   $$
--   \int y\,d\mu(y)=\frac{1}{n+1}\sum_{i=0}^{n}x_i
--   \quad\Longrightarrow\quad
--   \mu=\frac{1}{n+1}\sum_{i=0}^{n}\delta_{x_i}.
--   $$
--
--   The uniqueness of affine coordinates identifies the equal-mass measure in Theorem 1.10.
--
--   **Formalization Note** The paper states this in the standard simplex in $\mathbb R^{n+1}$; affine independence expresses the same uniqueness for vertices in $\mathbb R^n$.
-- source:
--   Lim & McCann, Geometrical bounds for the variance and recentered moments, arXiv:2001.11851v1, p. 15, Remark 3.2

import Mathlib
import Definitions.Def_IsodiamVar_Simplex_Defs

open MeasureTheory

namespace IsodiamVar.Simplex

/-- Remark 3.2: a measure on the vertices with their centroid as barycenter is uniform. -/
theorem remark_3_2 {n : ℕ} (x : Fin (n + 1) → E n)
    (hx : AffineIndependent ℝ x) (μ : Measure (E n))
    (hμ : InP (Set.range x) μ)
    (hb : (∫ y, y ∂μ) = ((n : ℝ) + 1)⁻¹ • ∑ i, x i) :
    μ = uniformVertexMeasure x := by sorry

end IsodiamVar.Simplex
