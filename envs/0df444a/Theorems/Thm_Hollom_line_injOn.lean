-- Prove2me | Theorems.Thm_Hollom_line_injOn
-- name    : Hollom.line_injOn
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T10:09:29.715805+00:00
-- url     : https://prove2.me/theorems/0306d3e0-6d17-4ab2-9de6-54ca01a69630
-- title:
--   Hollom: line inj On
-- statement:
--   The Hollom construction uses the line inj On property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/b-mehta/AharoniKorman/blob/ea16ed47faa49d6d815c8fb397b02e71b231781b/AharoniKorman/Counterexample.lean#L251-L269
-- source:
--   https://github.com/b-mehta/AharoniKorman/blob/ea16ed47faa49d6d815c8fb397b02e71b231781b/AharoniKorman/Counterexample.lean#L251-L269

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

theorem Hollom.line_injOn {C : Set Hollom} (n : ℕ) (hC : IsChain (· ≤ ·) C) (hCn : C ⊆ level n) :
    C.InjOn line := by sorry
