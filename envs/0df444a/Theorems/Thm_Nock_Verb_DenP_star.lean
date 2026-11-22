-- Prove2me | Theorems.Thm_Nock_Verb_DenP_star
-- name    : Nock.Verb.DenP_star
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:03:37.326619+00:00
-- url     : https://prove2.me/theorems/9479aa6c-4d5b-44e4-8412-08dfc63cace4
-- title:
--   Verb: Den P star
-- statement:
--   The Verb construction uses the Den P star property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureAgreement.lean#L436-L457
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureAgreement.lean#L436-L457

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

theorem Nock.Verb.DenP_star {l r x} : DenP (.node .star l r) x ↔ ∃ a b, DenP l a ∧ DenP r b ∧ EvP a b x := by sorry
