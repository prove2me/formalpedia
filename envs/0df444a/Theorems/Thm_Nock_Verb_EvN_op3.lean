-- Prove2me | Theorems.Thm_Nock_Verb_EvN_op3
-- name    : Nock.Verb.EvN_op3
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:11:32.004743+00:00
-- url     : https://prove2.me/theorems/55011816-a227-44d6-ad72-221d6bfc9fd7
-- title:
--   Verb: Ev N op3
-- statement:
--   The Verb construction uses the Ev N op3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Agreement.lean#L361-L372
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Agreement.lean#L361-L372

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

theorem Nock.Verb.EvN_op3 {subj tail x} : Ev subj (.cell (.atom 3) tail) x ↔
    ∃ y, Ev subj tail y ∧ x = Noun.wut y := by sorry
