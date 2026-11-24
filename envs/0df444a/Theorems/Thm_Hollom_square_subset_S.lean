-- Prove2me | Theorems.Thm_Hollom_square_subset_S
-- name    : Hollom.square_subset_S
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T10:10:14.385169+00:00
-- url     : https://prove2.me/theorems/512d6517-f997-4702-a25c-394f4bbbc0c2
-- title:
--   Hollom: square subset S
-- statement:
--   The Hollom construction uses the square subset S property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/b-mehta/AharoniKorman/blob/ea16ed47faa49d6d815c8fb397b02e71b231781b/AharoniKorman/Counterexample.lean#L1019-L1021
-- source:
--   https://github.com/b-mehta/AharoniKorman/blob/ea16ed47faa49d6d815c8fb397b02e71b231781b/AharoniKorman/Counterexample.lean#L1019-L1021

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

theorem Hollom.square_subset_S (h : (C ∩ level n).Finite) :
    ∀ᶠ a in atTop, embed n '' Set.Ici (a, a) ⊆ S n C \ (C ∩ level n) := by sorry
