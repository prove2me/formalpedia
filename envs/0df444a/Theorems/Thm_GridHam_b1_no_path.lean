-- Prove2me | Theorems.Thm_GridHam_b1_no_path
-- name    : GridHam.b1_no_path
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T21:47:39.287566+00:00
-- url     : https://prove2.me/theorems/d10cd3c6-7179-4fc4-b496-05538f2af253
-- title:
--   Grid Ham: b1 no path
-- statement:
--   **Base case B1.** On a 3-high grid no Hamiltonian path starts at `(1, 0)`
--   and ends in a column `≥ 3`: the forced opening leaves a path from `(0, 1)` on
--   the grid two columns narrower, which B0 rules out.
--
--   Source: https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/F3.lean#L498-L517
-- source:
--   https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/F3.lean#L498-L517

module
public import Definitions.Def_GridHam_StripSplit
public import Definitions.Def_GridHam_F3
set_option autoImplicit true
@[expose] public section
public section
open GridHam

theorem GridHam.b1_no_path (w : ℕ) (v : Coord) (hv : 3 ≤ v.1) : ¬ HasHamPath w 3 (1, 0) v := by sorry
