-- Prove2me | Theorems.Thm_NonbacktrackingWalk_card_one
-- name    : NonbacktrackingWalk.card_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T23:05:34.496778+00:00
-- url     : https://prove2.me/theorems/7229c3ef-2114-462c-9e5f-52a3f58abb04
-- title:
--   Nonbacktracking Walk: card one
-- statement:
--   The Nonbacktracking Walk construction uses the card one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benjamin-dozier/birthday-nonbacktracking/blob/7f4be1aae157cadcbb9511bd6b9ee187d60fb662/Solution.lean#L3717-L3719
-- source:
--   https://github.com/benjamin-dozier/birthday-nonbacktracking/blob/7f4be1aae157cadcbb9511bd6b9ee187d60fb662/Solution.lean#L3717-L3719

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

theorem NonbacktrackingWalk.card_one : Nat.card (NonbacktrackingWalk G start 1) = 1 := by sorry
