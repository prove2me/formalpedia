-- Prove2me | Theorems.Thm_Nock_Verb_ev2P
-- name    : Nock.Verb.ev2P
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:01:14.20691+00:00
-- url     : https://prove2.me/theorems/7524f23f-7678-4d01-b982-00f8547d7aa5
-- title:
--   Verb: ev2 P
-- statement:
--   The Verb construction uses the ev2 P property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureAgreement.lean#L163-L166
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureAgreement.lean#L163-L166

module
public import Definitions.Def_LeanPool_PureNock_Agreement
public import Definitions.Def_LeanPool_PureNock_Trace
public import Definitions.Def_LeanPool_PureNock_PaperReference
public import Mathlib.Tactic.IntervalCases
public import Definitions.Def_LeanPool_PureNock_PureAgreement
set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
open Noun

theorem Nock.Verb.ev2P {s1 f1 x1 s2 f2 x2} (h1 : EvP s1 f1 x1) (h2 : EvP s2 f2 x2) :
    ∃ f, evalPaper f s1 f1 = some x1 ∧ evalPaper f s2 f2 = some x2 := by sorry
