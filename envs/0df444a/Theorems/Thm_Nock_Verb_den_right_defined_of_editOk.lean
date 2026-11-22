-- Prove2me | Theorems.Thm_Nock_Verb_den_right_defined_of_editOk
-- name    : Nock.Verb.den_right_defined_of_editOk
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:15:34.190802+00:00
-- url     : https://prove2.me/theorems/a364bdd1-be0a-46ea-bc4a-790e57310f6b
-- title:
--   Verb: den right defined of edit Ok
-- statement:
--   The Verb construction uses the den right defined of edit Ok property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureCompleteHint.lean#L74-L104
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureCompleteHint.lean#L74-L104

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

theorem Nock.Verb.den_right_defined_of_editOk {a : Action} {l r : Verb} {f : Nat} {x : Noun}
    (hok : editOk (Verb.node a l r) = true) (h : den (f + 1) (Verb.node a l r) = some x) :
    ∃ g y, den g r = some y := by sorry
