-- Prove2me | Theorems.Thm_MiniFirstReturn_intervalPoint_injective
-- name    : MiniFirstReturn.intervalPoint_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T23:03:31.192811+00:00
-- url     : https://prove2.me/theorems/62a349ea-e861-4687-b1dc-84b0f9ac996a
-- title:
--   Mini First Return: interval Point injective
-- statement:
--   The Mini First Return construction uses the interval Point injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benjamin-dozier/birthday-nonbacktracking/blob/7f4be1aae157cadcbb9511bd6b9ee187d60fb662/Solution.lean#L924-L965
-- source:
--   https://github.com/benjamin-dozier/birthday-nonbacktracking/blob/7f4be1aae157cadcbb9511bd6b9ee187d60fb662/Solution.lean#L924-L965

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
noncomputable section
variable {V : Type*} [Fintype V]
variable (d : ℕ) [NeZero d]
variable (G : SimpleGraph V) (hG : IsRegularOfDegree G d)
attribute [local instance] graphAdjDecidable
attribute [local instance] vertexDecidableEq
open MiniFirstReturn
open scoped BigOperators
variable {X : Type*} [Fintype X] [DecidableEq X]

theorem MiniFirstReturn.intervalPoint_injective {I : Type*} [Fintype I]
    (p : Equiv.Perm X) (B : Finset X) (bases : I → B)
    (hbases : Function.Injective bases) :
    Function.Injective (intervalPoint p B bases) := by sorry
