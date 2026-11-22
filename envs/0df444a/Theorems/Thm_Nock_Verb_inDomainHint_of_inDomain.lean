-- Prove2me | Theorems.Thm_Nock_Verb_inDomainHint_of_inDomain
-- name    : Nock.Verb.inDomainHint_of_inDomain
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:15:23.012263+00:00
-- url     : https://prove2.me/theorems/81a40925-4dd9-4536-87a0-04dd312b2e0c
-- title:
--   Verb: in Domain Hint of in Domain
-- statement:
--   The Verb construction uses the in Domain Hint of in Domain property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureCompleteHint.lean#L43-L44
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureCompleteHint.lean#L43-L44

module
public import Definitions.Def_LeanPool_PureNock_PureComplete
public import Mathlib.Tactic.IntervalCases
public import Definitions.Def_LeanPool_PureNock_PureCompleteHint
set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
open Noun

theorem Nock.Verb.inDomainHint_of_inDomain {v : Verb} (h : inDomain v = true) : inDomainHint v = true := by sorry
