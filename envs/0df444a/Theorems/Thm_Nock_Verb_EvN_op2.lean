-- Prove2me | Theorems.Thm_Nock_Verb_EvN_op2
-- name    : Nock.Verb.EvN_op2
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:06:59.269732+00:00
-- url     : https://prove2.me/theorems/10328206-8e36-4224-b4f0-6ff1b4c566e2
-- title:
--   Verb: Ev N op2
-- statement:
--   The Verb construction uses the Ev N op2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Agreement.lean#L341-L359
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Agreement.lean#L341-L359

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

theorem Nock.Verb.EvN_op2 {subj tail x} : Ev subj (.cell (.atom 2) tail) x ↔
    ∃ hb hc sb sc, tail = .cell hb hc ∧ Ev subj hb sb ∧ Ev subj hc sc ∧ Ev sb sc x := by sorry
