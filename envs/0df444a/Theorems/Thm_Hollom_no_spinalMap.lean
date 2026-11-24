-- Prove2me | Theorems.Thm_Hollom_no_spinalMap
-- name    : Hollom.no_spinalMap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T10:12:43.580078+00:00
-- url     : https://prove2.me/theorems/f84e3eb8-33e9-425f-bea8-f0d4c68c58bf
-- title:
--   Hollom: no spinal Map
-- statement:
--   The Hollom partial order has no spinal maps.
--
--   Source: https://github.com/b-mehta/AharoniKorman/blob/ea16ed47faa49d6d815c8fb397b02e71b231781b/AharoniKorman/Counterexample.lean#L1239-L1243
-- source:
--   https://github.com/b-mehta/AharoniKorman/blob/ea16ed47faa49d6d815c8fb397b02e71b231781b/AharoniKorman/Counterexample.lean#L1239-L1243

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

theorem Hollom.no_spinalMap (hC : IsChain (· ≤ ·) C) (f : SpinalMap C) : False := by sorry
