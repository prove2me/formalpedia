-- Prove2me | Theorems.Thm_GridHam_pnext_unique_right
-- name    : GridHam.pnext_unique_right
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T21:40:49.105666+00:00
-- url     : https://prove2.me/theorems/781b2a2b-6ece-41a1-857e-e83b40f021a8
-- title:
--   Grid Ham: pnext unique right
-- statement:
--   The Grid Ham construction uses the pnext unique right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/F3.lean#L94-L100
-- source:
--   https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/F3.lean#L94-L100

module
public import Definitions.Def_GridHam_StripSplit
public import Definitions.Def_GridHam_F3
set_option autoImplicit true
@[expose] public section
public section
open GridHam

theorem GridHam.pnext_unique_right {p : List Coord} {x y y' : Coord} (hnd : p.Nodup)
    (h1 : PNext p x y) (h2 : PNext p x y') : y = y' := by sorry
