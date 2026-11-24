-- Prove2me | Theorems.Thm_GaussianPerimeter_VolumeComparison_weighted_amgm
-- name    : GaussianPerimeter.VolumeComparison.weighted_amgm
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T10:17:42.772585+00:00
-- url     : https://prove2.me/theorems/f05e0369-b7a5-4769-ae53-6743caaab735
-- title:
--   Volume Comparison: weighted amgm
-- statement:
--   The Volume Comparison construction uses the weighted amgm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/XinyuanXie-hub/GaussianPerimeter/blob/c54671095b3fdc672137addf46aa638c813db46a/GaussianPerimeter/PrekopaLeindler.lean#L221-L233
-- source:
--   https://github.com/XinyuanXie-hub/GaussianPerimeter/blob/c54671095b3fdc672137addf46aa638c813db46a/GaussianPerimeter/PrekopaLeindler.lean#L221-L233

module
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Definitions.Def_GaussianPerimeter_PrekopaHelpers
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Definitions.Def_GaussianPerimeter_PrekopaLeindler
set_option autoImplicit true
@[expose] public section
public section
open GaussianPerimeter GaussianPerimeter.VolumeComparison
open MeasureTheory Set
open scoped Pointwise

theorem GaussianPerimeter.VolumeComparison.weighted_amgm {θ a b : ℝ} (hθ : 0 < θ ∧ θ < 1) (ha : 0 ≤ a) (hb : 0 ≤ b)
    : ((1-θ)^(1-θ) * θ^θ)⁻¹ * a^(1-θ) * b^θ ≤ a + b := by sorry
