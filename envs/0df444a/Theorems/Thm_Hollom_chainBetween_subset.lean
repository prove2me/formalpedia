-- Prove2me | Theorems.Thm_Hollom_chainBetween_subset
-- name    : Hollom.chainBetween_subset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T10:09:29.654927+00:00
-- url     : https://prove2.me/theorems/7ed72831-a91c-4f1a-bde4-bc383d290abe
-- title:
--   Hollom: chain Between subset
-- statement:
--   The Hollom construction uses the chain Between subset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/b-mehta/AharoniKorman/blob/ea16ed47faa49d6d815c8fb397b02e71b231781b/AharoniKorman/Counterexample.lean#L615-L624
-- source:
--   https://github.com/b-mehta/AharoniKorman/blob/ea16ed47faa49d6d815c8fb397b02e71b231781b/AharoniKorman/Counterexample.lean#L615-L624

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

theorem Hollom.chainBetween_subset {a b c d : ℕ} :
    chainBetween a b c d ⊆ Finset.Icc (a, b) (c, d) := by sorry
