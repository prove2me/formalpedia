-- Prove2me | Theorems.Thm_Nock_Verb_Den_wut
-- name    : Nock.Verb.Den_wut
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:06:51.1628+00:00
-- url     : https://prove2.me/theorems/5003e981-cc20-4c61-a42e-b3f5da5718b0
-- title:
--   Verb: Den wut
-- statement:
--   The Verb construction uses the Den wut property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Agreement.lean#L286-L290
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Agreement.lean#L286-L290

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

theorem Nock.Verb.Den_wut {l r x} : ¬ Den (.node .wut l r) x := by sorry
