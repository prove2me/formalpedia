-- Prove2me | Theorems.Thm_GridHam_b0_no_path
-- name    : GridHam.b0_no_path
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T21:46:16.290523+00:00
-- url     : https://prove2.me/theorems/fc306cf5-348b-493b-91ba-18868a08de9c
-- title:
--   Grid Ham: b0 no path
-- statement:
--   **Base case B0.** On a 3-high grid no Hamiltonian path starts at `(0, 1)`
--   and ends in a column `≥ 1`.
--
--   Source: https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/F3.lean#L182-L220
-- source:
--   https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/F3.lean#L182-L220

module
public import Definitions.Def_GridHam_StripSplit
public import Definitions.Def_GridHam_F3
set_option autoImplicit true
@[expose] public section
public section
open GridHam

theorem GridHam.b0_no_path (w : ℕ) (v : Coord) (hv : 1 ≤ v.1) : ¬ HasHamPath w 3 (0, 1) v := by sorry
