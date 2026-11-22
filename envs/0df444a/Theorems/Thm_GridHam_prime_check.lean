-- Prove2me | Theorems.Thm_GridHam_prime_check
-- name    : GridHam.prime_check
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T22:00:54.983701+00:00
-- url     : https://prove2.me/theorems/c5171951-f1d4-4788-8e1d-6d9c3ae87f0e
-- title:
--   Grid Ham: prime check
-- statement:
--   Every acceptable problem on a prime shape has a valid stored path.
--
--   Source: https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/PrimeTable.lean#L669-L672
-- source:
--   https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/PrimeTable.lean#L669-L672

module
public import Definitions.Def_GridHam_StripSplit
public import Definitions.Def_GridHam_PrimeTable
set_option autoImplicit true
@[expose] public section
public section
open GridHam
set_option maxRecDepth 100000

theorem GridHam.prime_check : ∀ wh ∈ primeShapes, ∀ s ∈ allCoords wh.1 wh.2,
    ∀ t ∈ allCoords wh.1 wh.2, s ≠ t → IsAcceptable wh.1 wh.2 s t →
    ValidPath wh.1 wh.2 s t (primeLookup wh.1 wh.2 s t) := by sorry
