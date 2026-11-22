-- Prove2me | Theorems.Thm_GridHam_adjacent_swapXY
-- name    : GridHam.adjacent_swapXY
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T21:55:00.42562+00:00
-- url     : https://prove2.me/theorems/1a0031be-6a1e-4d14-acce-f27dcef89efa
-- title:
--   Grid Ham: adjacent swap XY
-- statement:
--   The Grid Ham construction uses the adjacent swap XY property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/StripSplit.lean#L363-L367
-- source:
--   https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/StripSplit.lean#L363-L367

module
public import Definitions.Def_GridHam_Forbidden
public import Definitions.Def_GridHam_StripSplit
set_option autoImplicit true
@[expose] public section
public section
open GridHam

theorem GridHam.adjacent_swapXY {v w : Coord} (h : Adjacent v w) : Adjacent (swapXY v) (swapXY w) := by sorry
