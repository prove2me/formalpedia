-- Prove2me | Theorems.Thm_GeneralFinalRatio_cutoff_mul_k_le
-- name    : GeneralFinalRatio.cutoff_mul_k_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T23:02:45.800922+00:00
-- url     : https://prove2.me/theorems/bb49b516-3bbb-548e-98dd-6de97faa3a90
-- title:
--   General Final Ratio: cutoff mul k le
-- statement:
--   The General Final Ratio construction uses the cutoff mul k le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benjamin-dozier/birthday-nonbacktracking/blob/7f4be1aae157cadcbb9511bd6b9ee187d60fb662/Solution.lean#L3834-L3842
-- source:
--   https://github.com/benjamin-dozier/birthday-nonbacktracking/blob/7f4be1aae157cadcbb9511bd6b9ee187d60fb662/Solution.lean#L3834-L3842

module
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Data.Int.Star
public import Mathlib.Combinatorics.Graph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Tactic.FinCases
public import Definitions.Def_BirthdayNonbacktracking_Solution
set_option autoImplicit true
@[expose] public section
public section
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSectionVars false
set_option linter.unusedSectionVars false
set_option linter.unusedSectionVars false
set_option linter.unusedSectionVars false
open GeneralFinalRatio

theorem GeneralFinalRatio.cutoff_mul_k_le (d n k : ℕ) (hkn : k < n) :
    cutoff d n k * k ≤ (64 * d + 1) * n := by sorry
