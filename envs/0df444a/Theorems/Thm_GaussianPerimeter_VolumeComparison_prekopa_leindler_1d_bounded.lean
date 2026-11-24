-- Prove2me | Theorems.Thm_GaussianPerimeter_VolumeComparison_prekopa_leindler_1d_bounded
-- name    : GaussianPerimeter.VolumeComparison.prekopa_leindler_1d_bounded
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T10:19:19.089282+00:00
-- url     : https://prove2.me/theorems/176ce7bd-286a-48f7-ad12-c6e3d89cbd3a
-- title:
--   Volume Comparison: prekopa leindler 1d bounded
-- statement:
--   The Volume Comparison construction uses the prekopa leindler 1d bounded property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/XinyuanXie-hub/GaussianPerimeter/blob/c54671095b3fdc672137addf46aa638c813db46a/GaussianPerimeter/PrekopaLeindler.lean#L364-L465
-- source:
--   https://github.com/XinyuanXie-hub/GaussianPerimeter/blob/c54671095b3fdc672137addf46aa638c813db46a/GaussianPerimeter/PrekopaLeindler.lean#L364-L465

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

theorem GaussianPerimeter.VolumeComparison.prekopa_leindler_1d_bounded {θ : ℝ} {f g h : ℝ → ENNReal}
    (hθ : 0 < θ ∧ θ < 1)
    (hf_measurable : Measurable f) (hf_bounded : iSup f ≠ ⊤)
    (hg_measurable : Measurable g) (hg_bounded : iSup g ≠ ⊤)
    (hh_measurable : Measurable h)
    (hfgh : ∀ x y, (f x) ^ (1 - θ) * (g y) ^ θ ≤ h (x + y))
    : ENNReal.ofReal (((1-θ)^(1-θ) * θ^θ)⁻¹) * (∫⁻ x, f x)^(1-θ) * (∫⁻ x, g x)^θ ≤ ∫⁻ x, h x := by sorry
