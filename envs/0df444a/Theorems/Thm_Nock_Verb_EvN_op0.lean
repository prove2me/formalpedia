-- Prove2me | Theorems.Thm_Nock_Verb_EvN_op0
-- name    : Nock.Verb.EvN_op0
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:04:26.747428+00:00
-- url     : https://prove2.me/theorems/605632ed-024d-40d4-89ef-0ed19a29737d
-- title:
--   Verb: Ev N op0
-- statement:
--   The Verb construction uses the Ev N op0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Agreement.lean#L319-L331
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Agreement.lean#L319-L331

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

theorem Nock.Verb.EvN_op0 {subj tail x} : Ev subj (.cell (.atom 0) tail) x ↔
    ∃ ax, tail = .atom ax ∧ Noun.slot ax subj = some x := by sorry
