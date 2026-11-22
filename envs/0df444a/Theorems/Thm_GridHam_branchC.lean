-- Prove2me | Theorems.Thm_GridHam_branchC
-- name    : GridHam.branchC
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T22:05:45.613674+00:00
-- url     : https://prove2.me/theorems/daf15259-57fb-4dea-85eb-dff6634bcb0c
-- title:
--   Grid Ham: branch C
-- statement:
--   **Branch (C).** `s` in column 0 or 1 and `t` at least three columns from
--   the right: the problem with the two rightmost columns removed is acceptable,
--   and column `w - 3` has a vertex that is neither endpoint.
--
--   Source: https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/Reduction.lean#L360-L396
-- source:
--   https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/Reduction.lean#L360-L396

module
public import Definitions.Def_GridHam_Arith
public import Definitions.Def_GridHam_PrimeTable
public import Definitions.Def_GridHam_Reduction
set_option autoImplicit true
@[expose] public section
public section
open GridHam

theorem GridHam.branchC (w h sx sy tx ty : ℕ) (hs : sx < w ∧ sy < h) (ht : tx < w ∧ ty < h)
    (hst : ¬ (sx = tx ∧ sy = ty)) (hwh : h ≤ w) (hle : sx ≤ tx) (hnp : NotPrime w h)
    (hacc : AccA w h sx sy tx ty) (hC1 : sx ≤ 1) (hC2 : tx + 2 < w) :
    AccA (w - 2) h sx sy tx ty ∧ FreeCol (w - 3) h sx sy tx ty := by sorry
