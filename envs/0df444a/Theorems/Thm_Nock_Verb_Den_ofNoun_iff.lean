-- Prove2me | Theorems.Thm_Nock_Verb_Den_ofNoun_iff
-- name    : Nock.Verb.Den_ofNoun_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:11:51.055061+00:00
-- url     : https://prove2.me/theorems/571e5328-b506-424b-a6b5-f93af7ea6e62
-- title:
--   Verb: Den of Noun iff
-- statement:
--   The Verb construction uses the Den of Noun iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Agreement.lean#L557-L558
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Agreement.lean#L557-L558

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

theorem Nock.Verb.Den_ofNoun_iff {n x} : Den (ofNoun n) x ↔ x = n := by sorry
