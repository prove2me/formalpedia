-- Prove2me | Theorems.Thm_Nock_Verb_den_left_defined
-- name    : Nock.Verb.den_left_defined
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:09:00.423797+00:00
-- url     : https://prove2.me/theorems/512a0dee-07b6-4178-a54a-614576a5b7eb
-- title:
--   Verb: den left defined
-- statement:
--   The Verb construction uses the den left defined property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureCompleteHint.lean#L60-L72
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureCompleteHint.lean#L60-L72

module
public import Definitions.Def_LeanPool_PureNock_PureComplete
public import Mathlib.Tactic.IntervalCases
public import Definitions.Def_LeanPool_PureNock_PureCompleteHint
set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
open Noun

theorem Nock.Verb.den_left_defined {a : Action} {l r : Verb} {f : Nat} {x : Noun}
    (h : den (f + 1) (Verb.node a l r) = some x) : ∃ y, den f l = some y := by sorry
