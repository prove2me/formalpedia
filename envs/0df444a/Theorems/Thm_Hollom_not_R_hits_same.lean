-- Prove2me | Theorems.Thm_Hollom_not_R_hits_same
-- name    : Hollom.not_R_hits_same
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T10:11:10.66025+00:00
-- url     : https://prove2.me/theorems/38a70d5d-d262-40e9-9aa0-dc0fc767b291
-- title:
--   Hollom: not R hits same
-- statement:
--   The Hollom construction uses the not R hits same property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/b-mehta/AharoniKorman/blob/ea16ed47faa49d6d815c8fb397b02e71b231781b/AharoniKorman/Counterexample.lean#L893-L897
-- source:
--   https://github.com/b-mehta/AharoniKorman/blob/ea16ed47faa49d6d815c8fb397b02e71b231781b/AharoniKorman/Counterexample.lean#L893-L897

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

theorem Hollom.not_R_hits_same {x : Hollom} (hx : x ∈ R n C) (hx' : x ∉ C ∩ level n) :
    f x ∉ C ∩ level n := by sorry
