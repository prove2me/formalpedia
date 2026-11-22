-- Prove2me | Theorems.Thm_GridHam_pnext_reverse
-- name    : GridHam.pnext_reverse
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T22:10:09.743146+00:00
-- url     : https://prove2.me/theorems/17f03942-888e-4de5-8369-8e2c3705372e
-- title:
--   Grid Ham: pnext reverse
-- statement:
--   The Grid Ham construction uses the pnext reverse property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/F3.lean#L531-L534
-- source:
--   https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/F3.lean#L531-L534

module
public import Definitions.Def_GridHam_StripSplit
public import Definitions.Def_GridHam_F3
set_option autoImplicit true
@[expose] public section
public section
open GridHam

theorem GridHam.pnext_reverse {p : List Coord} {x y : Coord} (h : PNext p x y) :
    PNext p.reverse y x := by sorry
