-- Prove2me | Theorems.Thm_GaussianPerimeter_VolumeComparison_iSup_rpow_of_pos
-- name    : GaussianPerimeter.VolumeComparison.iSup_rpow_of_pos
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T10:16:01.051458+00:00
-- url     : https://prove2.me/theorems/0d66b025-3999-400f-898e-d53f8d3a0a80
-- title:
--   Volume Comparison: i Sup rpow of pos
-- statement:
--   The Volume Comparison construction uses the i Sup rpow of pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/XinyuanXie-hub/GaussianPerimeter/blob/c54671095b3fdc672137addf46aa638c813db46a/GaussianPerimeter/PrekopaHelpers.lean#L58-L60
-- source:
--   https://github.com/XinyuanXie-hub/GaussianPerimeter/blob/c54671095b3fdc672137addf46aa638c813db46a/GaussianPerimeter/PrekopaHelpers.lean#L58-L60

module
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Definitions.Def_GaussianPerimeter_PrekopaHelpers
set_option autoImplicit true
@[expose] public section
public section
open GaussianPerimeter GaussianPerimeter.VolumeComparison

theorem GaussianPerimeter.VolumeComparison.iSup_rpow_of_pos {ι : Sort*} {r : ℝ} (hr : r > 0) (f : ι → ENNReal) :
    (⨆ (i : ι), f i) ^ r = ⨆ (i : ι), f i ^ r := by sorry
