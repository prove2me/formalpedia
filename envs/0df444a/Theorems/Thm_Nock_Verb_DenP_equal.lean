-- Prove2me | Theorems.Thm_Nock_Verb_DenP_equal
-- name    : Nock.Verb.DenP_equal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:05:16.224796+00:00
-- url     : https://prove2.me/theorems/6a00d98f-1bda-426a-8206-eb7d64afd688
-- title:
--   Verb: Den P equal
-- statement:
--   The Verb construction uses the Den P equal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureAgreement.lean#L475-L489
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureAgreement.lean#L475-L489

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

theorem Nock.Verb.DenP_equal {l r x} : DenP (.node .equal l r) x ↔
    ∃ a b, DenP l a ∧ DenP r b ∧ x = Noun.tis a b := by sorry
