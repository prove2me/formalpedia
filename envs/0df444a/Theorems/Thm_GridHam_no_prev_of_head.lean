-- Prove2me | Theorems.Thm_GridHam_no_prev_of_head
-- name    : GridHam.no_prev_of_head
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T21:44:53.388689+00:00
-- url     : https://prove2.me/theorems/ada105c0-ea8b-46be-8eb0-23ee44b4fdb4
-- title:
--   Grid Ham: no prev of head
-- statement:
--   The first cell of a path without repeats has no predecessor.
--
--   Source: https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/F3.lean#L114-L129
-- source:
--   https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/F3.lean#L114-L129

module
public import Definitions.Def_GridHam_StripSplit
public import Definitions.Def_GridHam_F3
set_option autoImplicit true
@[expose] public section
public section
open GridHam

theorem GridHam.no_prev_of_head {p : List Coord} {x y : Coord} (hnd : p.Nodup)
    (hh : p.head? = some x) (h : PNext p y x) : False := by sorry
