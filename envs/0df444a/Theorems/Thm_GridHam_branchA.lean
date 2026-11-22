-- Prove2me | Theorems.Thm_GridHam_branchA
-- name    : GridHam.branchA
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T22:04:44.081943+00:00
-- url     : https://prove2.me/theorems/762abee3-a77b-423c-af5e-14422f966ece
-- title:
--   Grid Ham: branch A
-- statement:
--   **Branch (A).** `s` at column ≥ 2: the problem with the two leftmost
--   columns removed is acceptable, and column 2 has a vertex that is neither
--   endpoint.
--
--   Source: https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/Reduction.lean#L311-L347
-- source:
--   https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/Reduction.lean#L311-L347

module
public import Definitions.Def_GridHam_Arith
public import Definitions.Def_GridHam_PrimeTable
public import Definitions.Def_GridHam_Reduction
set_option autoImplicit true
@[expose] public section
public section
open GridHam

theorem GridHam.branchA (w h sx sy tx ty : ℕ) (hs : sx < w ∧ sy < h) (ht : tx < w ∧ ty < h)
    (hst : ¬ (sx = tx ∧ sy = ty)) (hwh : h ≤ w) (hle : sx ≤ tx) (hnp : NotPrime w h)
    (hacc : AccA w h sx sy tx ty) (hA : 2 ≤ sx) :
    AccA (w - 2) h (sx - 2) sy (tx - 2) ty ∧ FreeCol 2 h sx sy tx ty := by sorry
