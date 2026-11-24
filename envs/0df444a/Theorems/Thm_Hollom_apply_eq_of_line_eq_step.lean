-- Prove2me | Theorems.Thm_Hollom_apply_eq_of_line_eq_step
-- name    : Hollom.apply_eq_of_line_eq_step
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T10:10:48.51489+00:00
-- url     : https://prove2.me/theorems/7509f02f-9a95-457f-9ce4-43b0ff60db7f
-- title:
--   Hollom: apply eq of line eq step
-- statement:
--   The important helper lemma to prove `apply_eq_of_line_eq`. That lemma says that given `(xl, yl, n)`
--   and `(xh, yh, n)` in a chain `C`, and two points `(a, b, n)` and `(c, d, n)` between them, if
--   `a + b = c + d` then a spinal map `f : SpinalMap C` sends them to the same place.
--   Here we show the special case where the two points are `(x + 1, y, n)` and `(x, y + 1, n)`, i.e.
--   they are beside each other.
--
--   Source: https://github.com/b-mehta/AharoniKorman/blob/ea16ed47faa49d6d815c8fb397b02e71b231781b/AharoniKorman/Counterexample.lean#L696-L778
-- source:
--   https://github.com/b-mehta/AharoniKorman/blob/ea16ed47faa49d6d815c8fb397b02e71b231781b/AharoniKorman/Counterexample.lean#L696-L778

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
open Finset

theorem Hollom.apply_eq_of_line_eq_step (f : SpinalMap C) {n xl yl xh yh : ℕ}
    (hC : IsChain (· ≤ ·) C)
    (hlo : h(xl, yl, n) ∈ C) (hhi : h(xh, yh, n) ∈ C) (hx : xl ≤ xh) (hy : yl ≤ yh)
    {x y : ℕ}
    (h₁l : h(xl, yl, n) ≤ h(x + 1, y, n)) (h₂l : h(xl, yl, n) ≤ h(x, y + 1, n))
    (h₁h : h(x + 1, y, n) ≤ h(xh, yh, n)) (h₂h : h(x, y + 1, n) ≤ h(xh, yh, n)) :
    f h(x + 1, y, n) = f h(x, y + 1, n) := by sorry
