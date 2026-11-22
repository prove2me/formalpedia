-- Prove2me | Theorems.Thm_Nock_Verb_EvP_op2
-- name    : Nock.Verb.EvP_op2
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:07:43.240139+00:00
-- url     : https://prove2.me/theorems/5b0b818f-9976-4d78-b8d2-dac15ee5386d
-- title:
--   Verb: Ev P op2
-- statement:
--   The Verb construction uses the Ev P op2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureAgreement.lean#L216-L234
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureAgreement.lean#L216-L234

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

theorem Nock.Verb.EvP_op2 {subj tail x} : EvP subj (.cell (.atom 2) tail) x ↔
    ∃ hb hc sb sc, tail = .cell hb hc ∧ EvP subj hb sb ∧ EvP subj hc sc ∧ EvP sb sc x := by sorry
