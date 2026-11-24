-- Prove2me | Theorems.Thm_GaussianPerimeter_inner_facetEmbedding
-- name    : GaussianPerimeter.inner_facetEmbedding
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T10:10:05.94549+00:00
-- url     : https://prove2.me/theorems/9d80e3ee-fa8f-4b14-bd57-a9cb2c3cb8a6
-- title:
--   Gaussian Perimeter: inner facet Embedding
-- statement:
--   The Gaussian Perimeter construction uses the inner facet Embedding property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/XinyuanXie-hub/GaussianPerimeter/blob/c54671095b3fdc672137addf46aa638c813db46a/GaussianPerimeter/Geometry.lean#L92-L95
-- source:
--   https://github.com/XinyuanXie-hub/GaussianPerimeter/blob/c54671095b3fdc672137addf46aa638c813db46a/GaussianPerimeter/Geometry.lean#L92-L95

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

theorem GaussianPerimeter.inner_facetEmbedding {k : ℕ} (u : Euc (k + 1)) (hu : ‖u‖ = 1)
    (ρ : ℝ) (y : Euc k) : ⟪u, facetEmbedding u hu ρ y⟫_ℝ = ρ := by sorry
