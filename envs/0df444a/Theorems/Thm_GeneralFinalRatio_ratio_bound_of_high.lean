-- Prove2me | Theorems.Thm_GeneralFinalRatio_ratio_bound_of_high
-- name    : GeneralFinalRatio.ratio_bound_of_high
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T23:06:20.02419+00:00
-- url     : https://prove2.me/theorems/e15668f3-4773-5671-ac10-e7f07ba36a1d
-- title:
--   General Final Ratio: ratio bound of high
-- statement:
--   Surround a high-regime switching proof by the trivial probability-at-most-one bound.
--
--   Source: https://github.com/benjamin-dozier/birthday-nonbacktracking/blob/7f4be1aae157cadcbb9511bd6b9ee187d60fb662/Solution.lean#L3891-L3905
-- source:
--   https://github.com/benjamin-dozier/birthday-nonbacktracking/blob/7f4be1aae157cadcbb9511bd6b9ee187d60fb662/Solution.lean#L3891-L3905

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

theorem GeneralFinalRatio.ratio_bound_of_high
    (d n k : ℕ) (p : ℝ) (hk : 0 < k) (hp_one : p ≤ 1)
    (hhigh : K d * n ≤ k ^ 2 →
      p ≤ (K d : ℝ) * (n : ℝ) / (k : ℝ) ^ 2) :
    p ≤ (K d : ℝ) * (n : ℝ) / (k : ℝ) ^ 2 := by sorry
