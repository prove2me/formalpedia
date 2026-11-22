-- Prove2me | Theorems.Thm_Nock_Verb_den_null_val
-- name    : Nock.Verb.den_null_val
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:08:59.10883+00:00
-- url     : https://prove2.me/theorems/9c14da0f-5a3d-4565-a2d3-3c6c3d61cfcb
-- title:
--   Verb: den null val
-- statement:
--   The Verb construction uses the den null val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureCompleteHint.lean#L223-L226
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureCompleteHint.lean#L223-L226

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

theorem Nock.Verb.den_null_val {A B : Verb} {f : Nat} {a b : Noun}
    (hA : den f A = some a) (hB : den f B = some b) :
    den (f + 1) (Verb.node .null A B) = some (Noun.cell a b) := by sorry
