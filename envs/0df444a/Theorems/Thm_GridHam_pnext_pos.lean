-- Prove2me | Theorems.Thm_GridHam_pnext_pos
-- name    : GridHam.pnext_pos
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T21:46:43.116197+00:00
-- url     : https://prove2.me/theorems/090c7549-aecd-4465-9c82-78536bc79516
-- title:
--   Grid Ham: pnext pos
-- statement:
--   If `x` sits at position `L` and `y` follows `x`, then `y` sits right after.
--
--   Source: https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/F3.lean#L225-L230
-- source:
--   https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/F3.lean#L225-L230

module
public import Definitions.Def_GridHam_StripSplit
public import Definitions.Def_GridHam_F3
set_option autoImplicit true
@[expose] public section
public section
open GridHam

theorem GridHam.pnext_pos {p L R : List Coord} {x y : Coord} (hnd : p.Nodup)
    (hp : p = L ++ x :: R) (h : PNext p x y) : ∃ R', R = y :: R' := by sorry
