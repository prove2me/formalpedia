-- Prove2me | Theorems.Thm_Hollom_square_subset_above
-- name    : Hollom.square_subset_above
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T10:11:00.764099+00:00
-- url     : https://prove2.me/theorems/6f54534a-839a-4685-a8d0-f748cf67c30a
-- title:
--   Hollom: square subset above
-- statement:
--   A helper lemma to show `square_subset_R`.  In particular shows that if `C ∩ level n` is finite, the
--   set of points `x` such that `x` is at least as large as every element of `C ∩ level n` contains an
--   "infinite square", i.e. a set of the form `{(x, y, n) | x ≥ a ∧ y ≥ a}`.
--   The precise statement here is stronger in two ways:
--   * Instead of showing that some `a` works, we instead show that any sufficiently large `a` work.
--     This is not much of a strengthening, but is convenient to have for chaining "sufficiently large"
--     choices later.
--   * We also exclude `C ∩ level n` itself on the right.
--
--   Source: https://github.com/b-mehta/AharoniKorman/blob/ea16ed47faa49d6d815c8fb397b02e71b231781b/AharoniKorman/Counterexample.lean#L850-L880
-- source:
--   https://github.com/b-mehta/AharoniKorman/blob/ea16ed47faa49d6d815c8fb397b02e71b231781b/AharoniKorman/Counterexample.lean#L850-L880

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

theorem Hollom.square_subset_above (h : (C ∩ level n).Finite) :
    ∀ᶠ a in atTop, embed n '' Set.Ici (a, a) ⊆ {x | ∀ y ∈ C ∩ level n, y ≤ x} \ (C ∩ level n) := by sorry
