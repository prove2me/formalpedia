-- Prove2me | Theorems.Thm_GaussianPerimeter_VolumeComparison_lintegral_fix_lintegral_eq_lintegral
-- name    : GaussianPerimeter.VolumeComparison.lintegral_fix_lintegral_eq_lintegral
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T10:20:47.727345+00:00
-- url     : https://prove2.me/theorems/cc71b609-614a-4f5d-98c3-b688667be054
-- title:
--   Volume Comparison: lintegral fix lintegral eq lintegral
-- statement:
--   The Volume Comparison construction uses the lintegral fix lintegral eq lintegral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/XinyuanXie-hub/GaussianPerimeter/blob/c54671095b3fdc672137addf46aa638c813db46a/GaussianPerimeter/PrekopaLeindler.lean#L574-L611
-- source:
--   https://github.com/XinyuanXie-hub/GaussianPerimeter/blob/c54671095b3fdc672137addf46aa638c813db46a/GaussianPerimeter/PrekopaLeindler.lean#L574-L611

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

theorem GaussianPerimeter.VolumeComparison.lintegral_fix_lintegral_eq_lintegral
    {d : ℕ} {f : (Fin (d + 2) → ℝ) → ENNReal} (hf_measurable : Measurable f) :
    ∫⁻ (x : Fin (d + 1) → ℝ), ∫⁻ (t : Fin 1 → ℝ), (fix f x) t
    = ∫⁻ (x : Fin (d + 2) → ℝ), f x := by sorry
