-- Prove2me | Theorems.Thm_Nock_Verb_EvN_op5
-- name    : Nock.Verb.EvN_op5
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:07:01.738531+00:00
-- url     : https://prove2.me/theorems/542c3567-89f8-4a17-b68a-760c4b8bbc01
-- title:
--   Verb: Ev N op5
-- statement:
--   The Verb construction uses the Ev N op5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Agreement.lean#L387-L405
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Agreement.lean#L387-L405

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

theorem Nock.Verb.EvN_op5 {subj tail x} : Ev subj (.cell (.atom 5) tail) x ↔
    ∃ hb hc sb sc, tail = .cell hb hc ∧ Ev subj hb sb ∧ Ev subj hc sc ∧ x = Noun.tis sb sc := by sorry
