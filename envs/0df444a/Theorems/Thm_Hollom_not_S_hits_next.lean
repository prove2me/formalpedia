-- Prove2me | Theorems.Thm_Hollom_not_S_hits_next
-- name    : Hollom.not_S_hits_next
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T10:12:08.561218+00:00
-- url     : https://prove2.me/theorems/ae852948-a692-428e-96b3-d8258342776f
-- title:
--   Hollom: not S hits next
-- statement:
--   Given a point `x` in `S` which is not in `C ∩ level n`, its image under `f` cannot be in
--   `C ∩ level (n + 1)`.
--
--   Source: https://github.com/b-mehta/AharoniKorman/blob/ea16ed47faa49d6d815c8fb397b02e71b231781b/AharoniKorman/Counterexample.lean#L1058-L1127
-- source:
--   https://github.com/b-mehta/AharoniKorman/blob/ea16ed47faa49d6d815c8fb397b02e71b231781b/AharoniKorman/Counterexample.lean#L1058-L1127

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

theorem Hollom.not_S_hits_next (f : SpinalMap C) (hC : IsChain (· ≤ ·) C)
    {x : Hollom} (hx : x ∈ S n C) (hx' : x ∉ C ∩ level n) :
    f x ∉ C ∩ level (n + 1) := by sorry
