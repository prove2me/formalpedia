-- Prove2me | Theorems.Thm_GridHam_mem_primeShapes_of
-- name    : GridHam.mem_primeShapes_of
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T22:04:13.569288+00:00
-- url     : https://prove2.me/theorems/51d2f646-65e5-40ae-bf7d-a98c53ef8711
-- title:
--   Grid Ham: mem prime Shapes of
-- statement:
--   A shape that is not `NotPrime` (and has both sides ≥ 1) is in `primeShapes`.
--
--   Source: https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/Reduction.lean#L275-L286
-- source:
--   https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/Reduction.lean#L275-L286

module
public import Definitions.Def_GridHam_Arith
public import Definitions.Def_GridHam_PrimeTable
public import Definitions.Def_GridHam_Reduction
set_option autoImplicit true
@[expose] public section
public section
open GridHam

theorem GridHam.mem_primeShapes_of (w h : ℕ) (hw : 1 ≤ w) (hh : 1 ≤ h) (hp : ¬ NotPrime w h) :
    (w, h) ∈ primeShapes := by sorry
