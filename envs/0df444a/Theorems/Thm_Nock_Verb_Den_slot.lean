-- Prove2me | Theorems.Thm_Nock_Verb_Den_slot
-- name    : Nock.Verb.Den_slot
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:03:07.772791+00:00
-- url     : https://prove2.me/theorems/a987b5e5-0c2c-4446-b1f7-9602a194a6ca
-- title:
--   Verb: Den slot
-- statement:
--   The Verb construction uses the Den slot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Agreement.lean#L210-L224
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Agreement.lean#L210-L224

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

theorem Nock.Verb.Den_slot {l r x} : Den (.node .slot l r) x ↔
    ∃ ax b, Den l (.atom ax) ∧ Den r b ∧ Noun.slot ax b = some x := by sorry
