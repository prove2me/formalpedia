-- Prove2me | Theorems.Thm_Hollom_SpinalMap_apply_mem_Icc_of_mem_Icc
-- name    : Hollom.SpinalMap.apply_mem_Icc_of_mem_Icc
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T10:10:38.158523+00:00
-- url     : https://prove2.me/theorems/7105e5bd-1c1d-4bee-93f9-22f8aada2f9e
-- title:
--   Spinal Map: apply mem Icc of mem Icc
-- statement:
--   The Spinal Map construction uses the apply mem Icc of mem Icc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/b-mehta/AharoniKorman/blob/ea16ed47faa49d6d815c8fb397b02e71b231781b/AharoniKorman/Counterexample.lean#L523-L525
-- source:
--   https://github.com/b-mehta/AharoniKorman/blob/ea16ed47faa49d6d815c8fb397b02e71b231781b/AharoniKorman/Counterexample.lean#L523-L525

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

theorem Hollom.SpinalMap.apply_mem_Icc_of_mem_Icc (hC : IsChain (· ≤ ·) C) (hy : y ∈ C) (hz : z ∈ C)
    (hx : x ∈ Set.Icc y z) : f x ∈ Set.Icc y z := by sorry
