-- Prove2me | Theorems.Thm_NonbacktrackingWalk_card_extension
-- name    : NonbacktrackingWalk.card_extension
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T23:05:50.247899+00:00
-- url     : https://prove2.me/theorems/dc053c3d-3e45-4725-9338-6a303403e95b
-- title:
--   Nonbacktracking Walk: card extension
-- statement:
--   The Nonbacktracking Walk construction uses the card extension property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benjamin-dozier/birthday-nonbacktracking/blob/7f4be1aae157cadcbb9511bd6b9ee187d60fb662/Solution.lean#L3558-L3567
-- source:
--   https://github.com/benjamin-dozier/birthday-nonbacktracking/blob/7f4be1aae157cadcbb9511bd6b9ee187d60fb662/Solution.lean#L3558-L3567

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
noncomputable section
variable {V : Type*} [Fintype V]
open NonbacktrackingWalk
variable {G : SimpleGraph V} {start : OrientedEdge G}

theorem NonbacktrackingWalk.card_extension {d : ℕ} (hG : IsRegularOfDegree G d) {k : ℕ}
    (w : NonbacktrackingWalk G start (k + 1)) : Nat.card (Extension w) = d - 1 := by sorry
