-- Prove2me | Theorems.Thm_GaussianPerimeter_VolumeComparison_prekopa_leindler
-- name    : GaussianPerimeter.VolumeComparison.prekopa_leindler
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T10:24:01.570338+00:00
-- url     : https://prove2.me/theorems/3e2b51d7-97a3-49f6-bddd-f68e500e7661
-- title:
--   Volume Comparison: prekopa leindler
-- statement:
--   The Volume Comparison construction uses the prekopa leindler property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/XinyuanXie-hub/GaussianPerimeter/blob/c54671095b3fdc672137addf46aa638c813db46a/GaussianPerimeter/PrekopaLeindler.lean#L632-L788
-- source:
--   https://github.com/XinyuanXie-hub/GaussianPerimeter/blob/c54671095b3fdc672137addf46aa638c813db46a/GaussianPerimeter/PrekopaLeindler.lean#L632-L788

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

theorem GaussianPerimeter.VolumeComparison.prekopa_leindler
    {d : ℕ} {θ : ℝ} {f g h : (Fin (d + 1) → ℝ) → ENNReal} (hθfgh : PLConditions (d + 1) θ f g h)
    : ENNReal.ofReal ((1 - θ) ^ ((d + 1) * (1 - θ)) * θ ^ ((d + 1) * θ))⁻¹
      * (∫⁻ x, f x) ^ (1 - θ) * (∫⁻ x, g x) ^ θ ≤ ∫⁻ x, h x := by sorry
