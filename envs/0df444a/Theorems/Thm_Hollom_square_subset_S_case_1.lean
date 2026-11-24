-- Prove2me | Theorems.Thm_Hollom_square_subset_S_case_1
-- name    : Hollom.square_subset_S_case_1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T10:11:40.165891+00:00
-- url     : https://prove2.me/theorems/03158e77-54bf-4abe-bde7-9dfeca8bdbd0
-- title:
--   Hollom: square subset S case 1
-- statement:
--   Assuming `C ∩ level n` is finite, and `C ∩ level (n + 1)` is finite, that there exists cofinitely
--   many `a` such that `{(x, y, n) | x ≥ a ∧ y ≥ a} ⊆ S \ (C ∩ level n)`.
--   We will later show the same assuming `C ∩ level (n + 1)` is infinite.
--
--   Source: https://github.com/b-mehta/AharoniKorman/blob/ea16ed47faa49d6d815c8fb397b02e71b231781b/AharoniKorman/Counterexample.lean#L974-L1005
-- source:
--   https://github.com/b-mehta/AharoniKorman/blob/ea16ed47faa49d6d815c8fb397b02e71b231781b/AharoniKorman/Counterexample.lean#L974-L1005

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

theorem Hollom.square_subset_S_case_1 (h : (C ∩ level n).Finite) (h' : (C ∩ level (n + 1)).Finite) :
    ∀ᶠ a in atTop, embed n '' Set.Ici (a, a) ⊆ S n C \ (C ∩ level n) := by sorry
