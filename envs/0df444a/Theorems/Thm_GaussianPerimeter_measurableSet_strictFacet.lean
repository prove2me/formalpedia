-- Prove2me | Theorems.Thm_GaussianPerimeter_measurableSet_strictFacet
-- name    : GaussianPerimeter.measurableSet_strictFacet
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T10:10:59.592138+00:00
-- url     : https://prove2.me/theorems/bd4896bd-73fe-4693-bbcc-9c43021a0f4e
-- title:
--   Gaussian Perimeter: measurable Set strict Facet
-- statement:
--   The Gaussian Perimeter construction uses the measurable Set strict Facet property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/XinyuanXie-hub/GaussianPerimeter/blob/c54671095b3fdc672137addf46aa638c813db46a/GaussianPerimeter/Geometry.lean#L142-L146
-- source:
--   https://github.com/XinyuanXie-hub/GaussianPerimeter/blob/c54671095b3fdc672137addf46aa638c813db46a/GaussianPerimeter/Geometry.lean#L142-L146

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
variable {k : ℕ} {ι : Type*}

theorem GaussianPerimeter.measurableSet_strictFacet [Countable ι] (u : ι → Euc (k + 1)) (ρ : ℝ) (i : ι) :
    MeasurableSet (strictFacet u ρ i) := by sorry
