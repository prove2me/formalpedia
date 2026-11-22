-- Prove2me | Theorems.Thm_Nock_Verb_EvN_op1
-- name    : Nock.Verb.EvN_op1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:11:30.561423+00:00
-- url     : https://prove2.me/theorems/fab7a7e6-3c64-4c0e-b3f8-11fd2921f0d2
-- title:
--   Verb: Ev N op1
-- statement:
--   The Verb construction uses the Ev N op1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Agreement.lean#L333-L339
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Agreement.lean#L333-L339

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

theorem Nock.Verb.EvN_op1 {subj tail x} : Ev subj (.cell (.atom 1) tail) x ↔ x = tail := by sorry
