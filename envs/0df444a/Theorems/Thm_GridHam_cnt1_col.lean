-- Prove2me | Theorems.Thm_GridHam_cnt1_col
-- name    : GridHam.cnt1_col
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T21:25:29.266547+00:00
-- url     : https://prove2.me/theorems/84cf37be-e2c9-44eb-bfa4-73f6dbb5f7fe
-- title:
--   Grid Ham: cnt1 col
-- statement:
--   Column `x` of a height-`h` grid has `(h + x % 2) / 2` cells of colour 1.
--
--   Source: https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/Coloring.lean#L230-L242
-- source:
--   https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/Coloring.lean#L230-L242

module
public import Definitions.Def_GridHam_Defs
public import Definitions.Def_GridHam_Coloring
set_option autoImplicit true
@[expose] public section
public section
open GridHam

theorem GridHam.cnt1_col (x : ℕ) : ∀ h, cnt1 ((List.range h).map (fun y => (x, y))) = (h + x % 2) / 2 := by sorry
