-- Prove2me | Theorems.Thm_Nock_Verb_EvN_op8
-- name    : Nock.Verb.EvN_op8
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:04:29.825308+00:00
-- url     : https://prove2.me/theorems/bd38e186-2bfc-4f7d-a27b-26098e225323
-- title:
--   Verb: Ev N op8
-- statement:
--   The Verb construction uses the Ev N op8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Agreement.lean#L426-L443
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Agreement.lean#L426-L443

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

theorem Nock.Verb.EvN_op8 {subj tail x} : Ev subj (.cell (.atom 8) tail) x ↔
    ∃ hb hc sb, tail = .cell hb hc ∧ Ev subj hb sb ∧ Ev (.cell sb subj) hc x := by sorry
