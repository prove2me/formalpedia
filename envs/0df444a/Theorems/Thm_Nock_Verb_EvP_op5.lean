-- Prove2me | Theorems.Thm_Nock_Verb_EvP_op5
-- name    : Nock.Verb.EvP_op5
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:07:43.648932+00:00
-- url     : https://prove2.me/theorems/6484d595-f058-46d1-88ef-3a795edf88db
-- title:
--   Verb: Ev P op5
-- statement:
--   The Verb construction uses the Ev P op5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureAgreement.lean#L262-L280
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureAgreement.lean#L262-L280

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

theorem Nock.Verb.EvP_op5 {subj tail x} : EvP subj (.cell (.atom 5) tail) x ↔
    ∃ hb hc sb sc, tail = .cell hb hc ∧ EvP subj hb sb ∧ EvP subj hc sc ∧ x = Noun.tis sb sc := by sorry
