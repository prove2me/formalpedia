-- Prove2me | Theorems.Thm_Nock_Verb_Den_null
-- name    : Nock.Verb.Den_null
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:04:22.406109+00:00
-- url     : https://prove2.me/theorems/e2c3d43b-d271-4e95-bac6-49c5e9f6c470
-- title:
--   Verb: Den null
-- statement:
--   The Verb construction uses the Den null property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Agreement.lean#L168-L185
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Agreement.lean#L168-L185

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

theorem Nock.Verb.Den_null {l r x} : Den (.node .null l r) x ↔ ∃ a b, x = .cell a b ∧ Den l a ∧ Den r b := by sorry
