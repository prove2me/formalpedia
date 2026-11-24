-- Prove2me | Theorems.Thm_Hollom_exists_partition_iff_nonempty_spinalMap
-- name    : Hollom.exists_partition_iff_nonempty_spinalMap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T10:10:40.716375+00:00
-- url     : https://prove2.me/theorems/025121d3-fcf5-43df-9f6b-43b268b06d65
-- title:
--   Hollom: exists partition iff nonempty spinal Map
-- statement:
--   Given a chain `C` in a partial order `α`, the existence of the following are equivalent:
--   * a partition of `α` into antichains, each which meets `C`
--   * a function `f : α → C` which is the identity on `C` and for which each fiber is an antichain
--
--   In fact, these two are in bijection, but we only need the weaker version that their existence
--   is equivalent.
--
--   Source: https://github.com/b-mehta/AharoniKorman/blob/ea16ed47faa49d6d815c8fb397b02e71b231781b/AharoniKorman/Counterexample.lean#L547-L567
-- source:
--   https://github.com/b-mehta/AharoniKorman/blob/ea16ed47faa49d6d815c8fb397b02e71b231781b/AharoniKorman/Counterexample.lean#L547-L567

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

theorem Hollom.exists_partition_iff_nonempty_spinalMap
    {α : Type*} [PartialOrder α] {C : Set α} (hC : IsChain (· ≤ ·) C) :
    (∃ S, Setoid.IsPartition S ∧ ∀ A ∈ S, IsAntichain (· ≤ ·) A ∧ (A ∩ C).Nonempty) ↔
      Nonempty (SpinalMap C) := by sorry
