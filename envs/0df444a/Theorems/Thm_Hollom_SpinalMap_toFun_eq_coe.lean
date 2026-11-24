-- Prove2me | Theorems.Thm_Hollom_SpinalMap_toFun_eq_coe
-- name    : Hollom.SpinalMap.toFun_eq_coe
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T10:09:11.274797+00:00
-- url     : https://prove2.me/theorems/896be3fb-6660-4a9c-aac6-43ae9fa73f8d
-- title:
--   Spinal Map: to Fun eq coe
-- statement:
--   The Spinal Map construction uses the to Fun eq coe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/b-mehta/AharoniKorman/blob/ea16ed47faa49d6d815c8fb397b02e71b231781b/AharoniKorman/Counterexample.lean#L469-L469
-- source:
--   https://github.com/b-mehta/AharoniKorman/blob/ea16ed47faa49d6d815c8fb397b02e71b231781b/AharoniKorman/Counterexample.lean#L469-L469

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

theorem Hollom.SpinalMap.toFun_eq_coe : f.toFun = f := by sorry

attribute [defeq] Hollom.SpinalMap.toFun_eq_coe
