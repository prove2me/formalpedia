-- Prove2me | Theorems.Thm_Nock_Verb_EvN_op4
-- name    : Nock.Verb.EvN_op4
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:07:01.744961+00:00
-- url     : https://prove2.me/theorems/7e5cba3f-1dc7-439b-87ac-f772a42d6863
-- title:
--   Verb: Ev N op4
-- statement:
--   The Verb construction uses the Ev N op4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Agreement.lean#L374-L385
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Agreement.lean#L374-L385

module
public import Definitions.Def_LeanPool_PureNock_Verb
public import Definitions.Def_LeanPool_PureNock_Semantics
public import Definitions.Def_LeanPool_PureNock_Agreement
set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
open Noun

theorem Nock.Verb.EvN_op4 {subj tail x} : Ev subj (.cell (.atom 4) tail) x ↔
    ∃ y, Ev subj tail y ∧ Noun.lus y = some x := by sorry
