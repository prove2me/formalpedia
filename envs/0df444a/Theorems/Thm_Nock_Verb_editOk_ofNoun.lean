-- Prove2me | Theorems.Thm_Nock_Verb_editOk_ofNoun
-- name    : Nock.Verb.editOk_ofNoun
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:07:15.982938+00:00
-- url     : https://prove2.me/theorems/f04fb6df-f84b-4ed7-ae1e-fdecd5943b12
-- title:
--   Verb: edit Ok of Noun
-- statement:
--   The Verb construction uses the edit Ok of Noun property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Agreement.lean#L568-L571
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Agreement.lean#L568-L571

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

theorem Nock.Verb.editOk_ofNoun (n : Noun) : editOk (ofNoun n) = true := by sorry
