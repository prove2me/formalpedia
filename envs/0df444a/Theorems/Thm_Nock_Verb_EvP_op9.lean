-- Prove2me | Theorems.Thm_Nock_Verb_EvP_op9
-- name    : Nock.Verb.EvP_op9
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:07:51.49626+00:00
-- url     : https://prove2.me/theorems/a158ead3-e7eb-4f12-9898-625e49b0cac1
-- title:
--   Verb: Ev P op9
-- statement:
--   The Verb construction uses the Ev P op9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureAgreement.lean#L356-L385
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureAgreement.lean#L356-L385

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

theorem Nock.Verb.EvP_op9 {subj tail x} : EvP subj (.cell (.atom 9) tail) x ↔
    ∃ ax c core arm, tail = .cell (.atom ax) c ∧ EvP subj c core ∧
      Noun.slot ax core = some arm ∧ EvP core arm x := by sorry
