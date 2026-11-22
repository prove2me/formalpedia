-- Prove2me | Theorems.Thm_GridHam_adjacent_symm
-- name    : GridHam.adjacent_symm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T21:42:30.641387+00:00
-- url     : https://prove2.me/theorems/6c7e5f5a-8a75-48fc-b3f3-8372bbd302da
-- title:
--   Grid Ham: adjacent symm
-- statement:
--   The Grid Ham construction uses the adjacent symm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/StripSplit.lean#L287-L289
-- source:
--   https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/StripSplit.lean#L287-L289

module
public import Definitions.Def_GridHam_Forbidden
public import Definitions.Def_GridHam_StripSplit
set_option autoImplicit true
@[expose] public section
public section
open GridHam

theorem GridHam.adjacent_symm {v w : Coord} (h : Adjacent v w) : Adjacent w v := by sorry
