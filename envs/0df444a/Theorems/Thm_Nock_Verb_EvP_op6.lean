-- Prove2me | Theorems.Thm_Nock_Verb_EvP_op6
-- name    : Nock.Verb.EvP_op6
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:07:46.627526+00:00
-- url     : https://prove2.me/theorems/98ac0bcf-b0d9-4241-8ad0-0b4f4147dc15
-- title:
--   Verb: Ev P op6
-- statement:
--   The Verb construction uses the Ev P op6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureAgreement.lean#L282-L316
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureAgreement.lean#L282-L316

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

theorem Nock.Verb.EvP_op6 {subj tail x} : EvP subj (.cell (.atom 6) tail) x ↔
    ∃ b c d cv, tail = .cell b (.cell c d) ∧ EvP subj b cv ∧
      ((cv = .atom 0 ∧ EvP subj c x) ∨ (cv = .atom 1 ∧ EvP subj d x)) := by sorry
