-- Prove2me | Theorems.Thm_Hollom_toHollom_le_toHollom
-- name    : Hollom.toHollom_le_toHollom
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T10:10:11.409693+00:00
-- url     : https://prove2.me/theorems/c8dd5253-2814-487b-85f9-9d054b7ae0e1
-- title:
--   Hollom: to Hollom le to Hollom
-- statement:
--   The Hollom construction uses the to Hollom le to Hollom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/b-mehta/AharoniKorman/blob/ea16ed47faa49d6d815c8fb397b02e71b231781b/AharoniKorman/Counterexample.lean#L174-L180
-- source:
--   https://github.com/b-mehta/AharoniKorman/blob/ea16ed47faa49d6d815c8fb397b02e71b231781b/AharoniKorman/Counterexample.lean#L174-L180

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

theorem Hollom.toHollom_le_toHollom {a b c d e f : ℕ} (h : (a, b) ≤ (d, e)) (hcf : f ≤ c) :
    h(a, b, c) ≤ h(d, e, f) := by sorry
