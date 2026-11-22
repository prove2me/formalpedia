-- Prove2me | Theorems.Thm_GridHam_adjacent_shiftX
-- name    : GridHam.adjacent_shiftX
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T21:53:47.286141+00:00
-- url     : https://prove2.me/theorems/97c2424d-c40c-460b-a0d6-5e712452ecee
-- title:
--   Grid Ham: adjacent shift X
-- statement:
--   The Grid Ham construction uses the adjacent shift X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/StripSplit.lean#L41-L46
-- source:
--   https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/StripSplit.lean#L41-L46

module
public import Definitions.Def_GridHam_Forbidden
public import Definitions.Def_GridHam_StripSplit
set_option autoImplicit true
@[expose] public section
public section
open GridHam

theorem GridHam.adjacent_shiftX (d : ℕ) {v w : Coord} (h : Adjacent v w) :
    Adjacent (shiftX d v) (shiftX d w) := by sorry
