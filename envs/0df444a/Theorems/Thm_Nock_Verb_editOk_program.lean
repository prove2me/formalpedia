-- Prove2me | Theorems.Thm_Nock_Verb_editOk_program
-- name    : Nock.Verb.editOk_program
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:02:23.294008+00:00
-- url     : https://prove2.me/theorems/ad921e4f-8a37-48b8-a98b-3ed56be1ad9e
-- title:
--   Verb: edit Ok program
-- statement:
--   The Verb construction uses the edit Ok program property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Agreement.lean#L573-L574
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Agreement.lean#L573-L574

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

theorem Nock.Verb.editOk_program (s f : Noun) : editOk (program s f) = true := by sorry
