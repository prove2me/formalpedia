-- Prove2me | Theorems.Thm_GridHam_pnext_unique_left
-- name    : GridHam.pnext_unique_left
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T21:41:38.452698+00:00
-- url     : https://prove2.me/theorems/299add68-40ce-45f8-b9da-1c7c454545de
-- title:
--   Grid Ham: pnext unique left
-- statement:
--   The Grid Ham construction uses the pnext unique left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/F3.lean#L102-L111
-- source:
--   https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/F3.lean#L102-L111

module
public import Definitions.Def_GridHam_StripSplit
public import Definitions.Def_GridHam_F3
set_option autoImplicit true
@[expose] public section
public section
open GridHam

theorem GridHam.pnext_unique_left {p : List Coord} {x y y' : Coord} (hnd : p.Nodup)
    (h1 : PNext p y x) (h2 : PNext p y' x) : y = y' := by sorry
