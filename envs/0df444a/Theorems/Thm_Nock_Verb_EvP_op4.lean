-- Prove2me | Theorems.Thm_Nock_Verb_EvP_op4
-- name    : Nock.Verb.EvP_op4
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:07:42.313472+00:00
-- url     : https://prove2.me/theorems/36e0fd7f-da30-4669-8a83-63d941ab38c8
-- title:
--   Verb: Ev P op4
-- statement:
--   The Verb construction uses the Ev P op4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureAgreement.lean#L249-L260
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureAgreement.lean#L249-L260

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

theorem Nock.Verb.EvP_op4 {subj tail x} : EvP subj (.cell (.atom 4) tail) x ↔
    ∃ y, EvP subj tail y ∧ Noun.lus y = some x := by sorry
