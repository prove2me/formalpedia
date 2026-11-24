-- Prove2me | Theorems.Thm_Hollom_exists_finite_intersection
-- name    : Hollom.exists_finite_intersection
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T10:10:22.711863+00:00
-- url     : https://prove2.me/theorems/c80b52e7-2ac8-4b2a-b587-f28c1cfbc02d
-- title:
--   Hollom: exists finite intersection
-- statement:
--   Show that every chain in the Hollom partial order has a finite intersection with infinitely many
--   levels.
--   This corresponds to Lemma 5.10 from the paper.
--
--   Source: https://github.com/b-mehta/AharoniKorman/blob/ea16ed47faa49d6d815c8fb397b02e71b231781b/AharoniKorman/Counterexample.lean#L386-L439
-- source:
--   https://github.com/b-mehta/AharoniKorman/blob/ea16ed47faa49d6d815c8fb397b02e71b231781b/AharoniKorman/Counterexample.lean#L386-L439

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

theorem Hollom.exists_finite_intersection (hC : IsChain (· ≤ ·) C) :
    ∃ᶠ n in atTop, (C ∩ level n).Finite := by sorry
