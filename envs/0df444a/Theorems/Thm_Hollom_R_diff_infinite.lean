-- Prove2me | Theorems.Thm_Hollom_R_diff_infinite
-- name    : Hollom.R_diff_infinite
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T10:17:05.394719+00:00
-- url     : https://prove2.me/theorems/3a9f72ea-44ed-4d0f-a1ff-d2d2fd7a8eb0
-- title:
--   Hollom: R diff infinite
-- statement:
--   The Hollom construction uses the R diff infinite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/b-mehta/AharoniKorman/blob/ea16ed47faa49d6d815c8fb397b02e71b231781b/AharoniKorman/Counterexample.lean#L888-L891
-- source:
--   https://github.com/b-mehta/AharoniKorman/blob/ea16ed47faa49d6d815c8fb397b02e71b231781b/AharoniKorman/Counterexample.lean#L888-L891

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

theorem Hollom.R_diff_infinite (h : (C ∩ level n).Finite) : (R n C \ (C ∩ level n)).Infinite := by sorry
