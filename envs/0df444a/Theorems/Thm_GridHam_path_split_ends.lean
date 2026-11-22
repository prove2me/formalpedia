-- Prove2me | Theorems.Thm_GridHam_path_split_ends
-- name    : GridHam.path_split_ends
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T21:48:23.228826+00:00
-- url     : https://prove2.me/theorems/6523dbc2-fccb-44df-877e-c10947179710
-- title:
--   Grid Ham: path split ends
-- statement:
--   Splitting a Hamiltonian path `s :: rest` into `s :: (m ++ [t])`.
--
--   Source: https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/Necessity.lean#L120-L139
-- source:
--   https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/Necessity.lean#L120-L139

module
public import Definitions.Def_GridHam_Arith
public import Definitions.Def_GridHam_StripSplit
public import Definitions.Def_GridHam_F3
public import Definitions.Def_GridHam_Necessity
set_option autoImplicit true
@[expose] public section
public section
open GridHam

theorem GridHam.path_split_ends {width height : ℕ} {s t : Coord} {p : List Coord}
    (hv : ValidPath width height s t p) (hbig : 2 ≤ width * height) :
    ∃ m, p = s :: (m ++ [t]) := by sorry
