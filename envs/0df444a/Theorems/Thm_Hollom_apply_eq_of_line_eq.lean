-- Prove2me | Theorems.Thm_Hollom_apply_eq_of_line_eq
-- name    : Hollom.apply_eq_of_line_eq
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T10:10:52.595711+00:00
-- url     : https://prove2.me/theorems/2a0cb818-9dbf-4192-8fee-9150a33a406a
-- title:
--   Hollom: apply eq of line eq
-- statement:
--   For two points of `C` in the same level, and two points `(a, b, n)` and `(c, d, n)` between them,
--   if `a + b = c + d` then `f (a, b, n) = f (c, d, n)`.
--
--   Source: https://github.com/b-mehta/AharoniKorman/blob/ea16ed47faa49d6d815c8fb397b02e71b231781b/AharoniKorman/Counterexample.lean#L810-L827
-- source:
--   https://github.com/b-mehta/AharoniKorman/blob/ea16ed47faa49d6d815c8fb397b02e71b231781b/AharoniKorman/Counterexample.lean#L810-L827

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

theorem Hollom.apply_eq_of_line_eq (f : SpinalMap C) {n : ℕ} (hC : IsChain (· ≤ ·) C)
    {lo hi : Hollom} (hlo : lo ∈ C ∩ level n) (hhi : hi ∈ C ∩ level n) (hlohi : lo ≤ hi)
    {x y : Hollom} (h : line x = line y)
    (h₁l : lo ≤ x) (h₂l : lo ≤ y) (h₁h : x ≤ hi) (h₂h : y ≤ hi) :
    f x = f y := by sorry
