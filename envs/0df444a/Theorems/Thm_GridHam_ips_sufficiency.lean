-- Prove2me | Theorems.Thm_GridHam_ips_sufficiency
-- name    : GridHam.ips_sufficiency
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T22:17:32.920053+00:00
-- url     : https://prove2.me/theorems/eb110bea-5f03-4a19-ac9e-e04b65af5263
-- title:
--   Grid Ham: ips sufficiency
-- statement:
--   **Sufficiency (IPS Theorem 3.2, ⇐).** Every acceptable problem with
--   `s ≠ t` has a Hamiltonian path.
--
--   Source: https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/Main.lean#L155-L160
-- source:
--   https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/Main.lean#L155-L160

module
public import Definitions.Def_GridHam_PrimeTable
public import Definitions.Def_GridHam_Arith
public import Definitions.Def_GridHam_StripSplit
public import Definitions.Def_GridHam_Reduction
public import Definitions.Def_GridHam_Necessity
public import Definitions.Def_GridHam_Main
set_option autoImplicit true
@[expose] public section
public section
open GridHam

theorem GridHam.ips_sufficiency (width height : ℕ) (s t : Coord)
    (hs : InBounds width height s) (ht : InBounds width height t)
    (hst : s ≠ t)
    (hacc : IsAcceptable width height s t) :
    HasHamPath width height s t := by sorry
