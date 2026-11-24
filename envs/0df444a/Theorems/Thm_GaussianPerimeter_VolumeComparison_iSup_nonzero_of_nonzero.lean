-- Prove2me | Theorems.Thm_GaussianPerimeter_VolumeComparison_iSup_nonzero_of_nonzero
-- name    : GaussianPerimeter.VolumeComparison.iSup_nonzero_of_nonzero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T10:13:58.393377+00:00
-- url     : https://prove2.me/theorems/a0e6e7fc-d7db-47d7-a695-77182c52e821
-- title:
--   Volume Comparison: i Sup nonzero of nonzero
-- statement:
--   The Volume Comparison construction uses the i Sup nonzero of nonzero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/XinyuanXie-hub/GaussianPerimeter/blob/c54671095b3fdc672137addf46aa638c813db46a/GaussianPerimeter/PrekopaHelpers.lean#L39-L43
-- source:
--   https://github.com/XinyuanXie-hub/GaussianPerimeter/blob/c54671095b3fdc672137addf46aa638c813db46a/GaussianPerimeter/PrekopaHelpers.lean#L39-L43

module
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Definitions.Def_GaussianPerimeter_PrekopaHelpers
set_option autoImplicit true
@[expose] public section
public section
open GaussianPerimeter GaussianPerimeter.VolumeComparison

theorem GaussianPerimeter.VolumeComparison.iSup_nonzero_of_nonzero {f : ℝ → ENNReal} (hf_nonzero : f ≠ 0) : iSup f ≠ 0 := by sorry
