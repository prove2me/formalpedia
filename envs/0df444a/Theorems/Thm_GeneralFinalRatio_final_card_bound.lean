-- Prove2me | Theorems.Thm_GeneralFinalRatio_final_card_bound
-- name    : GeneralFinalRatio.final_card_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T23:10:02.915896+00:00
-- url     : https://prove2.me/theorems/0d3638cf-c8f6-5df2-810c-b47c8639aecd
-- title:
--   General Final Ratio: final card bound
-- statement:
--   Final integral consequence of the generalized switching double count.
--
--   Source: https://github.com/benjamin-dozier/birthday-nonbacktracking/blob/7f4be1aae157cadcbb9511bd6b9ee187d60fb662/Solution.lean#L3845-L3875
-- source:
--   https://github.com/benjamin-dozier/birthday-nonbacktracking/blob/7f4be1aae157cadcbb9511bd6b9ee187d60fb662/Solution.lean#L3845-L3875

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

theorem GeneralFinalRatio.final_card_bound
    (d n k good plans : ℕ) (hd : 3 ≤ d) (hkn : k < n)
    (hinc : (d - 2) * k * good ≤
      8 * (d - 1) * cutoff d n k * plans) :
    good * k ^ 2 ≤ K d * n * plans := by sorry
