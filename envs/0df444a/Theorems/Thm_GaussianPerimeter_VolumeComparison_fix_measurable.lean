-- Prove2me | Theorems.Thm_GaussianPerimeter_VolumeComparison_fix_measurable
-- name    : GaussianPerimeter.VolumeComparison.fix_measurable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T10:08:47.035516+00:00
-- url     : https://prove2.me/theorems/2e199248-4020-4bb7-9a91-506389d6ba53
-- title:
--   Volume Comparison: fix measurable
-- statement:
--   The Volume Comparison construction uses the fix measurable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/XinyuanXie-hub/GaussianPerimeter/blob/c54671095b3fdc672137addf46aa638c813db46a/GaussianPerimeter/PrekopaLeindler.lean#L550-L553
-- source:
--   https://github.com/XinyuanXie-hub/GaussianPerimeter/blob/c54671095b3fdc672137addf46aa638c813db46a/GaussianPerimeter/PrekopaLeindler.lean#L550-L553

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

theorem GaussianPerimeter.VolumeComparison.fix_measurable {d : ℕ} {F : (Fin (d + 1) → ℝ) → ENNReal} (hF : Measurable F) (x : Fin d → ℝ)
    : Measurable (fix F x) := by sorry
