-- Prove2me | Theorems.Thm_Hollom_x0y0_mem
-- name    : Hollom.x0y0_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T10:10:10.884545+00:00
-- url     : https://prove2.me/theorems/972fe270-e3d9-44f8-b626-5f929006534f
-- title:
--   Hollom: x0y0 mem
-- statement:
--   The Hollom construction uses the x0y0 mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/b-mehta/AharoniKorman/blob/ea16ed47faa49d6d815c8fb397b02e71b231781b/AharoniKorman/Counterexample.lean#L913-L916
-- source:
--   https://github.com/b-mehta/AharoniKorman/blob/ea16ed47faa49d6d815c8fb397b02e71b231781b/AharoniKorman/Counterexample.lean#L913-L916

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

theorem Hollom.x0y0_mem (h : (C ∩ level (n + 1)).Nonempty) :
    embed (n + 1) (x0y0 n C) ∈ C := by sorry
