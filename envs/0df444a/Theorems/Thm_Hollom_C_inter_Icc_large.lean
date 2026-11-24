-- Prove2me | Theorems.Thm_Hollom_C_inter_Icc_large
-- name    : Hollom.C_inter_Icc_large
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T10:10:41.417063+00:00
-- url     : https://prove2.me/theorems/003cc8a1-88f1-4921-b76a-9eb8f63c6fff
-- title:
--   Hollom: C inter Icc large
-- statement:
--   The collection of points between `(xl, yl, n)` and `(xh, yh, n)` that are also in `C` has at least
--   `xh + yh + 1 - (xl + yl)` elements.
--   In other words, this collection must be a maximal chain relative to the interval it is contained in.
--   Note `card_C_inter_Icc_eq` strengthens this to an equality.
--
--   Source: https://github.com/b-mehta/AharoniKorman/blob/ea16ed47faa49d6d815c8fb397b02e71b231781b/AharoniKorman/Counterexample.lean#L644-L660
-- source:
--   https://github.com/b-mehta/AharoniKorman/blob/ea16ed47faa49d6d815c8fb397b02e71b231781b/AharoniKorman/Counterexample.lean#L644-L660

import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Data.Countable.Basic
import Mathlib.Data.Setoid.Partition
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Filter.AtTopBot.CompleteLattice
import Mathlib.Order.Interval.Set.Infinite
import Definitions.Def_AharoniKorman_ForMathlib_Misc
import Definitions.Def_AharoniKorman_Counterexample
set_option autoImplicit true
attribute [local aesop 2 simp] Set.subset_def Finset.subset_iff
open Hollom
local notation3 "h(" x ", " y ", " z ")" => toHollom (x, y, z)
variable {C : Set Hollom}
open Filter
variable {f : SpinalMap C}
open Classical Finset

theorem Hollom.C_inter_Icc_large (f : SpinalMap C) {n : ℕ} {xl yl xh yh : ℕ}
    (hC : IsChain (· ≤ ·) C)
    (hx : xl ≤ xh) (hy : yl ≤ yh)
    (hlo : h(xl, yl, n) ∈ C) (hhi : h(xh, yh, n) ∈ C) :
    xh + yh + 1 - (xl + yl) ≤ #{x ∈ (Icc (xl, yl) (xh, yh)).image (embed n) | x ∈ C} := by sorry
