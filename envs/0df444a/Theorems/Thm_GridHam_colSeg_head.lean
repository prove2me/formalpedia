-- Prove2me | Theorems.Thm_GridHam_colSeg_head
-- name    : GridHam.colSeg_head
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T21:42:46.822797+00:00
-- url     : https://prove2.me/theorems/81ed2187-ea91-422d-8f8b-70982e6e7d99
-- title:
--   Grid Ham: col Seg head
-- statement:
--   The Grid Ham construction uses the col Seg head property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/StripSplit.lean#L482-L485
-- source:
--   https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/StripSplit.lean#L482-L485

module
public import Definitions.Def_GridHam_Forbidden
public import Definitions.Def_GridHam_StripSplit
set_option autoImplicit true
@[expose] public section
public section
open GridHam

theorem GridHam.colSeg_head (c lo k : ℕ) : (colSeg c lo k).head? = some (c, lo + k) := by sorry
