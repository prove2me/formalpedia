-- Prove2me | Theorems.Thm_Nock_Verb_EvP_op10
-- name    : Nock.Verb.EvP_op10
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:07:53.898601+00:00
-- url     : https://prove2.me/theorems/25d34d2d-3945-484d-ac4c-072061a93c3d
-- title:
--   Verb: Ev P op10
-- statement:
--   The Verb construction uses the Ev P op10 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureAgreement.lean#L387-L407
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureAgreement.lean#L387-L407

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

theorem Nock.Verb.EvP_op10 {subj tail x} : EvP subj (.cell (.atom 10) tail) x ↔
    ∃ ax c d new old, tail = .cell (.cell (.atom ax) c) d ∧
      EvP subj c new ∧ EvP subj d old ∧ Noun.edit ax new old = some x := by sorry
