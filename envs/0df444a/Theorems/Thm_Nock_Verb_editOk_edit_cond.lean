-- Prove2me | Theorems.Thm_Nock_Verb_editOk_edit_cond
-- name    : Nock.Verb.editOk_edit_cond
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:02:33.065734+00:00
-- url     : https://prove2.me/theorems/7b87e84d-18bb-4ff3-8b87-76a14bdaf49d
-- title:
--   Verb: edit Ok edit cond
-- statement:
--   The Verb construction uses the edit Ok edit cond property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Agreement.lean#L1266-L1270
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Agreement.lean#L1266-L1270

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

theorem Nock.Verb.editOk_edit_cond {l r} (h : editOk (.node .edit l r) = true) : Verb.isPending r = false := by sorry
