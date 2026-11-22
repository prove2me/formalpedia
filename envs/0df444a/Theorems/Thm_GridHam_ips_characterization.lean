-- Prove2me | Theorems.Thm_GridHam_ips_characterization
-- name    : GridHam.ips_characterization
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T22:44:49.044258+00:00
-- url     : https://prove2.me/theorems/21f1eab5-9055-4aa0-9518-c630a1dc9912
-- title:
--   Grid Ham: ips characterization
-- statement:
--   **Main theorem.** IPS's characterization: a Hamiltonian path exists
--   between distinct vertices `s` and `t` of the `width × height` grid graph if
--   and only if the problem is acceptable (colour compatible and not forbidden).
--
--   The hypothesis `s ≠ t` is required: without it the statement is false (e.g.
--   on a 3×3 grid, `s = t = (0,0)` is `IsAcceptable` -- both endpoints have
--   parity 0 and no forbidden case applies -- but no Hamiltonian path starts and
--   ends at the same vertex of a 9-vertex grid). Only the sufficiency direction
--   needs it.
--
--   Source: https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/Main.lean#L171-L176
-- source:
--   https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/Main.lean#L171-L176

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

theorem GridHam.ips_characterization (width height : ℕ) (s t : Coord)
    (hs : InBounds width height s) (ht : InBounds width height t)
    (hst : s ≠ t) :
    HasHamPath width height s t ↔ IsAcceptable width height s t := by sorry
