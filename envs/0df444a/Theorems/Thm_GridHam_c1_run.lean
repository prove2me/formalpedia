-- Prove2me | Theorems.Thm_GridHam_c1_run
-- name    : GridHam.c1_run
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T22:10:46.036463+00:00
-- url     : https://prove2.me/theorems/32a17c0c-42fd-43da-830b-444eca50315c
-- title:
--   Grid Ham: c1 run
-- statement:
--   **The run (C1).** On a 3-high grid, a Hamiltonian path with both endpoints
--   in columns `≥ 2`, in which `(0, 1)` follows `(0, 0)`, contains one of two
--   8-cell runs through all of columns 0–1.
--
--   Source: https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/F3.lean#L665-L876
-- source:
--   https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/F3.lean#L665-L876

module
public import Definitions.Def_GridHam_StripSplit
public import Definitions.Def_GridHam_F3
set_option autoImplicit true
@[expose] public section
public section
open GridHam

theorem GridHam.c1_run (w : ℕ) (u v : Coord) (p : List Coord) (hu : 2 ≤ u.1) (hv2 : 2 ≤ v.1)
    (hvp : ValidPath w 3 u v p) (t1 : PNext p (0, 0) (0, 1)) :
    (∃ L R, p = L ++ (2, 1) :: (1, 1) :: (1, 0) :: (0, 0) :: (0, 1) :: (0, 2) :: (1, 2) :: (2, 2) :: R) ∨
    (∃ L R, p = L ++ (2, 0) :: (1, 0) :: (0, 0) :: (0, 1) :: (0, 2) :: (1, 2) :: (1, 1) :: (2, 1) :: R) := by sorry
