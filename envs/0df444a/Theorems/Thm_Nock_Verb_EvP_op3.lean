-- Prove2me | Theorems.Thm_Nock_Verb_EvP_op3
-- name    : Nock.Verb.EvP_op3
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:12:49.679002+00:00
-- url     : https://prove2.me/theorems/f8910fa2-fdb7-4c4b-a676-1c33b1aab30c
-- title:
--   Verb: Ev P op3
-- statement:
--   The Verb construction uses the Ev P op3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureAgreement.lean#L236-L247
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureAgreement.lean#L236-L247

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

theorem Nock.Verb.EvP_op3 {subj tail x} : EvP subj (.cell (.atom 3) tail) x ↔
    ∃ y, EvP subj tail y ∧ x = Noun.wut y := by sorry
