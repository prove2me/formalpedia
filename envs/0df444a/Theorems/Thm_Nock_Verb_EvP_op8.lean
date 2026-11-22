-- Prove2me | Theorems.Thm_Nock_Verb_EvP_op8
-- name    : Nock.Verb.EvP_op8
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:07:50.551808+00:00
-- url     : https://prove2.me/theorems/8aa1271f-e319-406f-b57e-e74309421be8
-- title:
--   Verb: Ev P op8
-- statement:
--   The Verb construction uses the Ev P op8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureAgreement.lean#L337-L354
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureAgreement.lean#L337-L354

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

theorem Nock.Verb.EvP_op8 {subj tail x} : EvP subj (.cell (.atom 8) tail) x ↔
    ∃ hb hc sb, tail = .cell hb hc ∧ EvP subj hb sb ∧ EvP (.cell sb subj) hc x := by sorry
