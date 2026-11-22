-- Prove2me | Theorems.Thm_GridHam_f2_width2_no_path
-- name    : GridHam.f2_width2_no_path
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T22:12:53.679414+00:00
-- url     : https://prove2.me/theorems/3825bab2-2565-495a-a208-c67002d27c66
-- title:
--   Grid Ham: f2 width2 no path
-- statement:
--   Forbidden case 2, width 2: `s`, `t` in the same interior row.
--
--   Source: https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/Necessity.lean#L142-L198
-- source:
--   https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/Necessity.lean#L142-L198

module
public import Definitions.Def_GridHam_Arith
public import Definitions.Def_GridHam_StripSplit
public import Definitions.Def_GridHam_F3
public import Definitions.Def_GridHam_Necessity
set_option autoImplicit true
@[expose] public section
public section
open GridHam

theorem GridHam.f2_width2_no_path (h : ℕ) (s t : Coord) (hsb : s.1 < 2 ∧ s.2 < h)
    (htb : t.1 < 2 ∧ t.2 < h) (hrow : s.2 = t.2) (hy0 : 0 < s.2) (hy1 : s.2 + 1 < h) :
    ¬ HasHamPath 2 h s t := by sorry
