-- Prove2me | Theorems.Thm_Hollom_SpinalMap_not_le_of_eq
-- name    : Hollom.SpinalMap.not_le_of_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T10:09:15.021162+00:00
-- url     : https://prove2.me/theorems/87d330c1-a1b9-44c0-a1cc-4f1e1790a979
-- title:
--   Spinal Map: not le of eq
-- statement:
--   The Spinal Map construction uses the not le of eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/b-mehta/AharoniKorman/blob/ea16ed47faa49d6d815c8fb397b02e71b231781b/AharoniKorman/Counterexample.lean#L479-L480
-- source:
--   https://github.com/b-mehta/AharoniKorman/blob/ea16ed47faa49d6d815c8fb397b02e71b231781b/AharoniKorman/Counterexample.lean#L479-L480

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

theorem Hollom.SpinalMap.not_le_of_eq (hfxy : f x = f y) (hxy : x ≠ y) : ¬ x ≤ y := by sorry
