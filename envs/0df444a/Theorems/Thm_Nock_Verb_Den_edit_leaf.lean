-- Prove2me | Theorems.Thm_Nock_Verb_Den_edit_leaf
-- name    : Nock.Verb.Den_edit_leaf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:06:47.819222+00:00
-- url     : https://prove2.me/theorems/fd79f243-b755-42b4-a47d-dddaf90ddc06
-- title:
--   Verb: Den edit leaf
-- statement:
--   The Verb construction uses the Den edit leaf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Agreement.lean#L280-L284
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Agreement.lean#L280-L284

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

theorem Nock.Verb.Den_edit_leaf {l k x} : ¬ Den (.node .edit l (.leaf k)) x := by sorry
