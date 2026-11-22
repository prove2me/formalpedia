-- Prove2me | Theorems.Thm_GridHam_c2_prefix
-- name    : GridHam.c2_prefix
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T22:08:16.880531+00:00
-- url     : https://prove2.me/theorems/b632ea35-90bd-42bb-b07d-e27c49e2778e
-- title:
--   Grid Ham: c2 prefix
-- statement:
--   **Forced opening (C2).** On a 3-high grid, a Hamiltonian path from `(1, 0)`
--   to a cell in column `≥ 2` begins `(1,0),(0,0),(0,1),(0,2),(1,2),(1,1),(2,1)`.
--
--   Source: https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/F3.lean#L346-L493
-- source:
--   https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/F3.lean#L346-L493

module
public import Definitions.Def_GridHam_StripSplit
public import Definitions.Def_GridHam_F3
set_option autoImplicit true
@[expose] public section
public section
open GridHam

theorem GridHam.c2_prefix (w : ℕ) (v : Coord) (p : List Coord) (hv2 : 2 ≤ v.1)
    (hvp : ValidPath w 3 (1, 0) v p) :
    ∃ R, p = (1, 0) :: (0, 0) :: (0, 1) :: (0, 2) :: (1, 2) :: (1, 1) :: (2, 1) :: R := by sorry
