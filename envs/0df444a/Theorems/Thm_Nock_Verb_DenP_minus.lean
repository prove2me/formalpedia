-- Prove2me | Theorems.Thm_Nock_Verb_DenP_minus
-- name    : Nock.Verb.DenP_minus
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:03:45.616946+00:00
-- url     : https://prove2.me/theorems/b81f2b92-0b1a-4e29-b897-dd974b489c67
-- title:
--   Verb: Den P minus
-- statement:
--   The Verb construction uses the Den P minus property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureAgreement.lean#L491-L511
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureAgreement.lean#L491-L511

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

theorem Nock.Verb.DenP_minus {l r x} : DenP (.node .minus l r) x ↔
    ∃ b, DenP r b ∧ ((DenP l (.atom 3) ∧ x = Noun.wut b) ∨ (DenP l (.atom 4) ∧ Noun.lus b = some x))
      := by sorry
