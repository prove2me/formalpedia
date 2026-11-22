-- Prove2me | Theorems.Thm_Nock_Verb_Den_equal
-- name    : Nock.Verb.Den_equal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:04:21.135813+00:00
-- url     : https://prove2.me/theorems/66e7bc49-2833-4b9a-b593-91735af71c47
-- title:
--   Verb: Den equal
-- statement:
--   The Verb construction uses the Den equal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Agreement.lean#L226-L240
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Agreement.lean#L226-L240

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

theorem Nock.Verb.Den_equal {l r x} : Den (.node .equal l r) x ↔
    ∃ a b, Den l a ∧ Den r b ∧ x = Noun.tis a b := by sorry
