-- Prove2me | Theorems.Thm_Nock_Verb_EvP_op0
-- name    : Nock.Verb.EvP_op0
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:07:38.649321+00:00
-- url     : https://prove2.me/theorems/7951634f-ee83-4136-a11e-3c240f31bbbf
-- title:
--   Verb: Ev P op0
-- statement:
--   The Verb construction uses the Ev P op0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureAgreement.lean#L194-L206
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureAgreement.lean#L194-L206

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

theorem Nock.Verb.EvP_op0 {subj tail x} : EvP subj (.cell (.atom 0) tail) x ↔
    ∃ ax, tail = .atom ax ∧ Noun.slot ax subj = some x := by sorry
