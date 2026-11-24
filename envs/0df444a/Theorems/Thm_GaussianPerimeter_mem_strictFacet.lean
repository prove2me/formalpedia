-- Prove2me | Theorems.Thm_GaussianPerimeter_mem_strictFacet
-- name    : GaussianPerimeter.mem_strictFacet
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T10:11:02.091+00:00
-- url     : https://prove2.me/theorems/bde48ce4-6660-43f8-9153-31b2f642aced
-- title:
--   Gaussian Perimeter: mem strict Facet
-- statement:
--   The Gaussian Perimeter construction uses the mem strict Facet property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/XinyuanXie-hub/GaussianPerimeter/blob/c54671095b3fdc672137addf46aa638c813db46a/GaussianPerimeter/Geometry.lean#L137-L140
-- source:
--   https://github.com/XinyuanXie-hub/GaussianPerimeter/blob/c54671095b3fdc672137addf46aa638c813db46a/GaussianPerimeter/Geometry.lean#L137-L140

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

theorem GaussianPerimeter.mem_strictFacet (u : ι → Euc (k + 1)) (ρ : ℝ) (i : ι) (x : Euc (k + 1)) :
    x ∈ strictFacet u ρ i ↔
      ⟪u i, x⟫_ℝ = ρ ∧ ∀ j ≠ i, ⟪u j, x⟫_ℝ < ρ := by sorry
