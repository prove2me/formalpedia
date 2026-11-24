-- Prove2me | Theorems.Thm_Hollom_add_lt_add_of_lt
-- name    : Hollom.add_lt_add_of_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T10:10:19.843819+00:00
-- url     : https://prove2.me/theorems/0aa4a91b-2611-426d-ab28-e67aabc73a67
-- title:
--   Hollom: add lt add of lt
-- statement:
--   The Hollom construction uses the add lt add of lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/b-mehta/AharoniKorman/blob/ea16ed47faa49d6d815c8fb397b02e71b231781b/AharoniKorman/Counterexample.lean#L271-L274
-- source:
--   https://github.com/b-mehta/AharoniKorman/blob/ea16ed47faa49d6d815c8fb397b02e71b231781b/AharoniKorman/Counterexample.lean#L271-L274

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

theorem Hollom.add_lt_add_of_lt {a b c d n : ℕ} (h : h(a, b, n) < h(c, d, n)) : a + b < c + d := by sorry
