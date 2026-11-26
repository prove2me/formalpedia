-- Prove2me | Theorems.Thm_GeneralFinalRatio_ratio_bound
-- name    : GeneralFinalRatio.ratio_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T23:06:19.308403+00:00
-- url     : https://prove2.me/theorems/f1fc6a41-5de7-427e-9239-26a0b629c4c9
-- title:
--   General Final Ratio: ratio bound
-- statement:
--   Cast the integral bound to the probability ratio.
--
--   Source: https://github.com/benjamin-dozier/birthday-nonbacktracking/blob/7f4be1aae157cadcbb9511bd6b9ee187d60fb662/Solution.lean#L3878-L3888
-- source:
--   https://github.com/benjamin-dozier/birthday-nonbacktracking/blob/7f4be1aae157cadcbb9511bd6b9ee187d60fb662/Solution.lean#L3878-L3888

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

theorem GeneralFinalRatio.ratio_bound
    (d n k good plans : ℕ) (hk : 0 < k) (hplans : 0 < plans)
    (hcard : good * k ^ 2 ≤ K d * n * plans) :
    (good : ℝ) / (plans : ℝ) ≤
      (K d : ℝ) * (n : ℝ) / (k : ℝ) ^ 2 := by sorry
