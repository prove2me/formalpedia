-- Prove2me | Theorems.Thm_Nock_Verb_den_terminal_val
-- name    : Nock.Verb.den_terminal_val
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:03:59.973247+00:00
-- url     : https://prove2.me/theorems/be3c775b-5cd7-4f40-871d-d6fe1b9d99c9
-- title:
--   Verb: den terminal val
-- statement:
--   The Verb construction uses the den terminal val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureCompleteHint.lean#L190-L192
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureCompleteHint.lean#L190-L192

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

theorem Nock.Verb.den_terminal_val {v : Verb} {F : Nat} {y : Noun}
    (ht : isTerminal v = true) (h : den F v = some y) : y = v.noun := by sorry
