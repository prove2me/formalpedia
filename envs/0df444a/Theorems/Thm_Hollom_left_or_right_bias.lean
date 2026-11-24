-- Prove2me | Theorems.Thm_Hollom_left_or_right_bias
-- name    : Hollom.left_or_right_bias
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T10:11:57.700137+00:00
-- url     : https://prove2.me/theorems/a230a858-6e60-4f63-bff4-10abffbaf7e0
-- title:
--   Hollom: left or right bias
-- statement:
--   Given `(a, b, n)` which is a lower bound on `C ∩ level n`, and assuming `C ∩ level n` is infinite,
--   we either have:
--   * for any `i`, there is an element of `C ∩ level n` greater than `(a, i, n)`
--   * for any `i`, there is an element of `C ∩ level n` greater than `(i, b, n)`
--
--   Source: https://github.com/b-mehta/AharoniKorman/blob/ea16ed47faa49d6d815c8fb397b02e71b231781b/AharoniKorman/Counterexample.lean#L1034-L1052
-- source:
--   https://github.com/b-mehta/AharoniKorman/blob/ea16ed47faa49d6d815c8fb397b02e71b231781b/AharoniKorman/Counterexample.lean#L1034-L1052

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
variable {n : ℕ}

theorem Hollom.left_or_right_bias {n : ℕ} (a b : ℕ)
    (hab : ∀ x y, h(x, y, n) ∈ C → h(a, b, n) ≤ h(x, y, n))
    (hCn : (C ∩ level n).Infinite) :
    (∀ i : ℕ, ∃ j ∈ C ∩ level n, h(a, i, n) ≤ j) ∨
    (∀ i : ℕ, ∃ j ∈ C ∩ level n, h(i, b, n) ≤ j) := by sorry
