-- Prove2me | Theorems.Thm_Nock_Verb_Den_leaf
-- name    : Nock.Verb.Den_leaf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:06:40.543458+00:00
-- url     : https://prove2.me/theorems/d591ce6a-f167-4d68-ac9e-d3fc9ee51085
-- title:
--   Verb: Den leaf
-- statement:
--   The Verb construction uses the Den leaf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Agreement.lean#L163-L166
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Agreement.lean#L163-L166

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

theorem Nock.Verb.Den_leaf {k x} : Den (.leaf k) x ↔ x = .atom k := by sorry
