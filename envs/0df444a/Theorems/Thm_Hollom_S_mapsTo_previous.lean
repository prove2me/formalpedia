-- Prove2me | Theorems.Thm_Hollom_S_mapsTo_previous
-- name    : Hollom.S_mapsTo_previous
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T10:12:06.510782+00:00
-- url     : https://prove2.me/theorems/01f081b1-7ff1-415f-b8cf-dba7d2d481ff
-- title:
--   Hollom: S maps To previous
-- statement:
--   Every element of `S \ (C ∩ level n)` must be mapped into `C ∩ level (n - 1)`.
--
--   Source: https://github.com/b-mehta/AharoniKorman/blob/ea16ed47faa49d6d815c8fb397b02e71b231781b/AharoniKorman/Counterexample.lean#L1130-L1170
-- source:
--   https://github.com/b-mehta/AharoniKorman/blob/ea16ed47faa49d6d815c8fb397b02e71b231781b/AharoniKorman/Counterexample.lean#L1130-L1170

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

theorem Hollom.S_mapsTo_previous (f : SpinalMap C) (hC : IsChain (· ≤ ·) C) (hn : n ≠ 0) :
    ∀ x ∈ S n C \ (C ∩ level n), f x ∈ C ∩ level (n - 1) := by sorry
