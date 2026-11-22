-- Prove2me | Theorems.Thm_GridHam_c1_contract
-- name    : GridHam.c1_contract
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T22:10:58.225171+00:00
-- url     : https://prove2.me/theorems/55273b07-abbe-4298-9d46-c421e18493bb
-- title:
--   Grid Ham: c1 contract
-- statement:
--   **Contraction step.** On a 3-high grid, a Hamiltonian path with both
--   endpoints in columns `≥ 2` gives one on the grid two columns narrower, with
--   both endpoints shifted two columns left.
--
--   Source: https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/F3.lean#L881-L969
-- source:
--   https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/F3.lean#L881-L969

module
public import Definitions.Def_GridHam_StripSplit
public import Definitions.Def_GridHam_F3
set_option autoImplicit true
@[expose] public section
public section
open GridHam

theorem GridHam.c1_contract (w : ℕ) (u v : Coord) (hu : 2 ≤ u.1) (hv : 2 ≤ v.1)
    (h : HasHamPath w 3 u v) : HasHamPath (w - 2) 3 (shiftL2 u) (shiftL2 v) := by sorry
