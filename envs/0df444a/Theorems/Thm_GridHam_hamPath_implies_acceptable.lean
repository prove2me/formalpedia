-- Prove2me | Theorems.Thm_GridHam_hamPath_implies_acceptable
-- name    : GridHam.hamPath_implies_acceptable
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T22:15:15.22628+00:00
-- url     : https://prove2.me/theorems/674ea877-d255-4f22-89c1-5f3b8f7fc931
-- title:
--   Grid Ham: ham Path implies acceptable
-- statement:
--   **Necessity, assembled (IPS Theorem 3.1).** If a Hamiltonian path exists,
--   the problem is acceptable.
--
--   Source: https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/Necessity.lean#L321-L331
-- source:
--   https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/Necessity.lean#L321-L331

module
public import Definitions.Def_GridHam_Arith
public import Definitions.Def_GridHam_StripSplit
public import Definitions.Def_GridHam_F3
public import Definitions.Def_GridHam_Necessity
set_option autoImplicit true
@[expose] public section
public section
open GridHam

theorem GridHam.hamPath_implies_acceptable (width height : ℕ) (s t : Coord)
    (hs : InBounds width height s) (ht : InBounds width height t)
    (h : HasHamPath width height s t) :
    IsAcceptable width height s t := by sorry
