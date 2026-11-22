-- Prove2me | Theorems.Thm_Nock_Verb_EvP_op1
-- name    : Nock.Verb.EvP_op1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:12:45.338188+00:00
-- url     : https://prove2.me/theorems/7d2d6f93-39e3-4574-9818-d8be192ad8b9
-- title:
--   Verb: Ev P op1
-- statement:
--   The Verb construction uses the Ev P op1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureAgreement.lean#L208-L214
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureAgreement.lean#L208-L214

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

theorem Nock.Verb.EvP_op1 {subj tail x} : EvP subj (.cell (.atom 1) tail) x ↔ x = tail := by sorry
