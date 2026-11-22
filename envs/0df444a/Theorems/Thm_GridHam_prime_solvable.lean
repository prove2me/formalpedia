-- Prove2me | Theorems.Thm_GridHam_prime_solvable
-- name    : GridHam.prime_solvable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T22:01:52.504784+00:00
-- url     : https://prove2.me/theorems/d8ff76e7-219a-4cb0-9596-c0b32941721b
-- title:
--   Grid Ham: prime solvable
-- statement:
--   **Base case.** Acceptable problems on prime shapes are solvable.
--
--   Source: https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/PrimeTable.lean#L675-L680
-- source:
--   https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/PrimeTable.lean#L675-L680

module
public import Definitions.Def_GridHam_StripSplit
public import Definitions.Def_GridHam_PrimeTable
set_option autoImplicit true
@[expose] public section
public section
open GridHam

theorem GridHam.prime_solvable (w h : ℕ) (s t : Coord) (hshape : (w, h) ∈ primeShapes)
    (hs : InBounds w h s) (ht : InBounds w h t) (hst : s ≠ t)
    (hacc : IsAcceptable w h s t) : HasHamPath w h s t := by sorry
