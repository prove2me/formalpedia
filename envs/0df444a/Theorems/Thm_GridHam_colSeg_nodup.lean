-- Prove2me | Theorems.Thm_GridHam_colSeg_nodup
-- name    : GridHam.colSeg_nodup
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T21:56:23.970806+00:00
-- url     : https://prove2.me/theorems/f4c422f8-80d7-4416-99b6-35a5b4531204
-- title:
--   Grid Ham: col Seg nodup
-- statement:
--   The Grid Ham construction uses the col Seg nodup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/StripSplit.lean#L543-L554
-- source:
--   https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/StripSplit.lean#L543-L554

module
public import Definitions.Def_GridHam_Forbidden
public import Definitions.Def_GridHam_StripSplit
set_option autoImplicit true
@[expose] public section
public section
open GridHam

theorem GridHam.colSeg_nodup (c lo : ℕ) : ∀ k, (colSeg c lo k).Nodup := by sorry
