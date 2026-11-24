-- Prove2me | Theorems.Thm_GaussianPerimeter_VolumeComparison_lintegral_eq_vol_superlevelset_lintegral_01
-- name    : GaussianPerimeter.VolumeComparison.lintegral_eq_vol_superlevelset_lintegral_01
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T10:16:55.847793+00:00
-- url     : https://prove2.me/theorems/dd331a89-5b2e-473a-9637-2c54d6edd179
-- title:
--   Volume Comparison: lintegral eq vol superlevelset lintegral 01
-- statement:
--   The Volume Comparison construction uses the lintegral eq vol superlevelset lintegral 01 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/XinyuanXie-hub/GaussianPerimeter/blob/c54671095b3fdc672137addf46aa638c813db46a/GaussianPerimeter/PrekopaLeindler.lean#L195-L218
-- source:
--   https://github.com/XinyuanXie-hub/GaussianPerimeter/blob/c54671095b3fdc672137addf46aa638c813db46a/GaussianPerimeter/PrekopaLeindler.lean#L195-L218

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

theorem GaussianPerimeter.VolumeComparison.lintegral_eq_vol_superlevelset_lintegral_01
    {f : ℝ → ENNReal} (hf_bound : f ≤ 1) (hf_measurable : Measurable f)
    : ∫⁻ x, f x = ∫⁻ t in Ioo 0 1, (fun t ↦ volume {x | ENNReal.ofReal t ≤ f x}) t := by sorry
