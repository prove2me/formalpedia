-- Prove2me | Theorems.Thm_Hollom_not_S_mapsTo_previous
-- name    : Hollom.not_S_mapsTo_previous
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T10:12:15.514618+00:00
-- url     : https://prove2.me/theorems/025ed005-3a05-49f0-8bd5-2a30027cdbc0
-- title:
--   Hollom: not S maps To previous
-- statement:
--   Supposing that all of `S \ (C ∩ level n)` is sent to `C ∩ level (n - 1)`, we deduce a contradiction.
--
--   Source: https://github.com/b-mehta/AharoniKorman/blob/ea16ed47faa49d6d815c8fb397b02e71b231781b/AharoniKorman/Counterexample.lean#L1176-L1236
-- source:
--   https://github.com/b-mehta/AharoniKorman/blob/ea16ed47faa49d6d815c8fb397b02e71b231781b/AharoniKorman/Counterexample.lean#L1176-L1236

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
open Finset

theorem Hollom.not_S_mapsTo_previous (hC : IsChain (· ≤ ·) C)
    (hCn : (C ∩ level n).Finite) (hn : n ≠ 0)
    (h : ∀ x ∈ S n C \ (C ∩ level n), f x ∈ C ∩ level (n - 1)) :
    False := by sorry
