-- Prove2me | Theorems.Thm_GridHam_colSeg_last
-- name    : GridHam.colSeg_last
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T21:55:41.541272+00:00
-- url     : https://prove2.me/theorems/dfda6bae-635e-4ad8-a8d8-9f714816daa5
-- title:
--   Grid Ham: col Seg last
-- statement:
--   The Grid Ham construction uses the col Seg last property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/StripSplit.lean#L487-L496
-- source:
--   https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/StripSplit.lean#L487-L496

module
public import Definitions.Def_GridHam_Forbidden
public import Definitions.Def_GridHam_StripSplit
set_option autoImplicit true
@[expose] public section
public section
open GridHam

theorem GridHam.colSeg_last (c lo : ℕ) : ∀ k, (colSeg c lo k).getLast? = some (c, lo) := by sorry
