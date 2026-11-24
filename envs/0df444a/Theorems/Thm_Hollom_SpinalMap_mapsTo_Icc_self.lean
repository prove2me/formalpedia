-- Prove2me | Theorems.Thm_Hollom_SpinalMap_mapsTo_Icc_self
-- name    : Hollom.SpinalMap.mapsTo_Icc_self
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T10:09:47.385133+00:00
-- url     : https://prove2.me/theorems/c354e1bc-7af6-47e9-8310-849f5aab87dc
-- title:
--   Spinal Map: maps To Icc self
-- statement:
--   The Spinal Map construction uses the maps To Icc self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/b-mehta/AharoniKorman/blob/ea16ed47faa49d6d815c8fb397b02e71b231781b/AharoniKorman/Counterexample.lean#L527-L528
-- source:
--   https://github.com/b-mehta/AharoniKorman/blob/ea16ed47faa49d6d815c8fb397b02e71b231781b/AharoniKorman/Counterexample.lean#L527-L528

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

theorem Hollom.SpinalMap.mapsTo_Icc_self (hC : IsChain (· ≤ ·) C) (hy : y ∈ C) (hz : z ∈ C) :
    Set.MapsTo f (Set.Icc y z) (Set.Icc y z) := by sorry
