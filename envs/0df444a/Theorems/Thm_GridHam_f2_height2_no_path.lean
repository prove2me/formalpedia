-- Prove2me | Theorems.Thm_GridHam_f2_height2_no_path
-- name    : GridHam.f2_height2_no_path
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T22:13:21.232806+00:00
-- url     : https://prove2.me/theorems/8545b45b-42a1-4fc7-a664-a9b2e667a262
-- title:
--   Grid Ham: f2 height2 no path
-- statement:
--   Forbidden case 2, height 2: `s`, `t` in the same interior column.
--
--   Source: https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/Necessity.lean#L201-L257
-- source:
--   https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/Necessity.lean#L201-L257

module
public import Definitions.Def_GridHam_Arith
public import Definitions.Def_GridHam_StripSplit
public import Definitions.Def_GridHam_F3
public import Definitions.Def_GridHam_Necessity
set_option autoImplicit true
@[expose] public section
public section
open GridHam

theorem GridHam.f2_height2_no_path (w : ℕ) (s t : Coord) (hsb : s.1 < w ∧ s.2 < 2)
    (htb : t.1 < w ∧ t.2 < 2) (hcol : s.1 = t.1) (hx0 : 0 < s.1) (hx1 : s.1 + 1 < w) :
    ¬ HasHamPath w 2 s t := by sorry
