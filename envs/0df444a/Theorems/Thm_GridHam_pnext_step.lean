-- Prove2me | Theorems.Thm_GridHam_pnext_step
-- name    : GridHam.pnext_step
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T22:09:04.219212+00:00
-- url     : https://prove2.me/theorems/72bf4b6b-76b8-457c-88c2-9346e8fb421f
-- title:
--   Grid Ham: pnext step
-- statement:
--   The Grid Ham construction uses the pnext step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/F3.lean#L526-L529
-- source:
--   https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/F3.lean#L526-L529

module
public import Definitions.Def_GridHam_StripSplit
public import Definitions.Def_GridHam_F3
set_option autoImplicit true
@[expose] public section
public section
open GridHam

theorem GridHam.pnext_step {p L R : List Coord} {x y : Coord} (hnd : p.Nodup)
    (hp : p = L ++ x :: R) (h : PNext p x y) : ∃ R', p = (L ++ [x]) ++ y :: R' := by sorry
