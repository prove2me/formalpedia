-- Prove2me | Theorems.Thm_Nock_Verb_DenP_slot
-- name    : Nock.Verb.DenP_slot
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:03:36.971729+00:00
-- url     : https://prove2.me/theorems/3145c1e7-07fb-423d-8772-48d770344dda
-- title:
--   Verb: Den P slot
-- statement:
--   The Verb construction uses the Den P slot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureAgreement.lean#L459-L473
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureAgreement.lean#L459-L473

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

theorem Nock.Verb.DenP_slot {l r x} : DenP (.node .slot l r) x ↔
    ∃ ax b, DenP l (.atom ax) ∧ DenP r b ∧ Noun.slot ax b = some x := by sorry
