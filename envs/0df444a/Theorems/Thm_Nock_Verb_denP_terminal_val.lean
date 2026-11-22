-- Prove2me | Theorems.Thm_Nock_Verb_denP_terminal_val
-- name    : Nock.Verb.denP_terminal_val
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:03:54.019176+00:00
-- url     : https://prove2.me/theorems/ce1dfeca-d4ee-4f0d-bbf3-664951775e06
-- title:
--   Verb: den P terminal val
-- statement:
--   The Verb construction uses the den P terminal val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureComplete.lean#L74-L76
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureComplete.lean#L74-L76

module
public import Definitions.Def_LeanPool_PureNock_PureAgreement
public import Mathlib.Tactic.IntervalCases
public import Definitions.Def_LeanPool_PureNock_PureComplete
set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
open Noun

theorem Nock.Verb.denP_terminal_val {v : Verb} {F : Nat} {y : Noun}
    (ht : isTerminal v = true) (h : denP F v = some y) : y = v.noun := by sorry
