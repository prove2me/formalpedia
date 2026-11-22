-- Prove2me | Theorems.Thm_GridHam_split_unique
-- name    : GridHam.split_unique
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T21:30:55.266875+00:00
-- url     : https://prove2.me/theorems/a3c7dfa2-951f-4afb-883c-dcaeb25281ae
-- title:
--   Grid Ham: split unique
-- statement:
--   In a list without repeats, an element sits at only one position.
--
--   Source: https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/F3.lean#L58-L92
-- source:
--   https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/F3.lean#L58-L92

module
public import Definitions.Def_GridHam_StripSplit
public import Definitions.Def_GridHam_F3
set_option autoImplicit true
@[expose] public section
public section
open GridHam

theorem GridHam.split_unique : ∀ (l1 l1' r r' : List Coord) (x : Coord),
    (l1 ++ x :: r).Nodup → l1 ++ x :: r = l1' ++ x :: r' → l1 = l1' ∧ r = r' := by sorry
