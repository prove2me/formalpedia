-- Prove2me | Theorems.Thm_GridHam_hasHamPath_reverse
-- name    : GridHam.hasHamPath_reverse
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T21:28:29.099013+00:00
-- url     : https://prove2.me/theorems/2e0793b2-0c0a-4162-b7e7-2b76cff13a19
-- title:
--   Grid Ham: has Ham Path reverse
-- statement:
--   Reversing a Hamiltonian path swaps its endpoints.
--
--   Source: https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/StripSplit.lean#L342-L358
-- source:
--   https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/StripSplit.lean#L342-L358

module
public import Definitions.Def_GridHam_Forbidden
public import Definitions.Def_GridHam_StripSplit
set_option autoImplicit true
@[expose] public section
public section
open GridHam

theorem GridHam.hasHamPath_reverse {width height : ℕ} {s t : Coord}
    (h : HasHamPath width height s t) : HasHamPath width height t s := by sorry
