-- Prove2me | Theorems.Thm_GaussianPerimeter_isometry_facetEmbedding
-- name    : GaussianPerimeter.isometry_facetEmbedding
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T12:18:04.270913+00:00
-- url     : https://prove2.me/theorems/a46db9bf-5898-469e-ab29-41922741a5d2
-- title:
--   Gaussian Perimeter: isometry facet Embedding
-- statement:
--   The Gaussian Perimeter construction uses the isometry facet Embedding property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/XinyuanXie-hub/GaussianPerimeter/blob/c54671095b3fdc672137addf46aa638c813db46a/GaussianPerimeter/Geometry.lean#L97-L103
-- source:
--   https://github.com/XinyuanXie-hub/GaussianPerimeter/blob/c54671095b3fdc672137addf46aa638c813db46a/GaussianPerimeter/Geometry.lean#L97-L103

module
public import Definitions.Def_GaussianPerimeter_Definitions
public import Mathlib.MeasureTheory.Integral.Lebesgue.Map
public import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
public import Definitions.Def_GaussianPerimeter_Geometry
set_option autoImplicit true
@[expose] public section
public section
open Function Set MeasureTheory MeasureTheory.Measure
open scoped ENNReal InnerProductSpace RealInnerProductSpace Function
open GaussianPerimeter
local notation "Euc" k => EuclideanSpace ℝ (Fin k)

theorem GaussianPerimeter.isometry_facetEmbedding {k : ℕ} (u : Euc (k + 1)) (hu : ‖u‖ = 1)
    (ρ : ℝ) : Isometry (facetEmbedding u hu ρ) := by sorry
