-- Prove2me | Theorems.Thm_Hollom_SpinalMap_le_apply_of_le
-- name    : Hollom.SpinalMap.le_apply_of_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T10:10:29.191882+00:00
-- url     : https://prove2.me/theorems/75913588-aaa1-40ce-8854-d50c47a8db6d
-- title:
--   Spinal Map: le apply of le
-- statement:
--   The Spinal Map construction uses the le apply of le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/b-mehta/AharoniKorman/blob/ea16ed47faa49d6d815c8fb397b02e71b231781b/AharoniKorman/Counterexample.lean#L495-L500
-- source:
--   https://github.com/b-mehta/AharoniKorman/blob/ea16ed47faa49d6d815c8fb397b02e71b231781b/AharoniKorman/Counterexample.lean#L495-L500

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
variable {α : Type*} [PartialOrder α] {C : Set α}
open Hollom.SpinalMap
variable (f : SpinalMap C)
variable {x y z : α}

theorem Hollom.SpinalMap.le_apply_of_le (hC : IsChain (· ≤ ·) C) (hy : y ∈ C) (hx : y ≤ x) : y ≤ f x := by sorry
