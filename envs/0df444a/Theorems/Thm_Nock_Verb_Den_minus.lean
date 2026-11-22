-- Prove2me | Theorems.Thm_Nock_Verb_Den_minus
-- name    : Nock.Verb.Den_minus
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:03:09.368723+00:00
-- url     : https://prove2.me/theorems/a57b0820-8f6d-4cac-b9f0-1da52dd69e09
-- title:
--   Verb: Den minus
-- statement:
--   The Verb construction uses the Den minus property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Agreement.lean#L242-L262
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Agreement.lean#L242-L262

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

theorem Nock.Verb.Den_minus {l r x} : Den (.node .minus l r) x ↔
    ∃ b, Den r b ∧ ((Den l (.atom 3) ∧ x = Noun.wut b) ∨ (Den l (.atom 4) ∧ Noun.lus b = some x)) := by sorry
