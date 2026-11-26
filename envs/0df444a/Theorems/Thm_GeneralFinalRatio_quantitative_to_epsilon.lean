-- Prove2me | Theorems.Thm_GeneralFinalRatio_quantitative_to_epsilon
-- name    : GeneralFinalRatio.quantitative_to_epsilon
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T23:06:35.662333+00:00
-- url     : https://prove2.me/theorems/e7c08da7-2bcf-493f-82e7-5806f86a8b8e
-- title:
--   General Final Ratio: quantitative to epsilon
-- statement:
--   A convenient purely real conversion from the quantitative `K(d)n/k²`
--   bound to the existential square-root threshold in the paper.
--
--   Source: https://github.com/benjamin-dozier/birthday-nonbacktracking/blob/7f4be1aae157cadcbb9511bd6b9ee187d60fb662/Solution.lean#L3909-L3947
-- source:
--   https://github.com/benjamin-dozier/birthday-nonbacktracking/blob/7f4be1aae157cadcbb9511bd6b9ee187d60fb662/Solution.lean#L3909-L3947

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

theorem GeneralFinalRatio.quantitative_to_epsilon (d : ℕ) (hd : 3 ≤ d) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (n k : ℕ) (p : ℝ),
        p ≤ (K d : ℝ) * (n : ℝ) / (k : ℝ) ^ 2 →
        C * Real.sqrt (n : ℝ) < (k : ℝ) → p < ε := by sorry
