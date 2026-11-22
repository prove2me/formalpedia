-- Prove2me | Theorems.Thm_GridHam_branchB
-- name    : GridHam.branchB
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T22:06:12.146801+00:00
-- url     : https://prove2.me/theorems/f879b4cd-5b2c-4768-9c49-db8784b70801
-- title:
--   Grid Ham: branch B
-- statement:
--   **Branch (B).** `s` in column 0 or 1 and `t` in one of the last two
--   columns: splitting after column 1 at row `rChoice` gives two acceptable
--   pieces, the left one `2 × h` from `s` to `(1, r)`, the right one `(w-2) × h`
--   from `(0, r)` to `t` shifted left by 2.
--
--   Source: https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/Reduction.lean#L425-L482
-- source:
--   https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/Reduction.lean#L425-L482

module
public import Definitions.Def_GridHam_Arith
public import Definitions.Def_GridHam_PrimeTable
public import Definitions.Def_GridHam_Reduction
set_option autoImplicit true
@[expose] public section
public section
open GridHam
set_option maxHeartbeats 4000000

theorem GridHam.branchB (w h sx sy tx ty : ℕ) (hs : sx < w ∧ sy < h) (ht : tx < w ∧ ty < h)
    (hst : ¬ (sx = tx ∧ sy = ty)) (hwh : h ≤ w) (hle : sx ≤ tx) (hnp : NotPrime w h)
    (hacc : AccA w h sx sy tx ty) (hB1 : sx ≤ 1) (hB2 : w ≤ tx + 2) :
    BConcl w h sx sy tx ty (rChoice sx sy h) := by sorry
