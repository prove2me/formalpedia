-- Prove2me | Theorems.Thm_Nock_Verb_editOk_children
-- name    : Nock.Verb.editOk_children
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:00:21.118616+00:00
-- url     : https://prove2.me/theorems/f4de5a01-88c1-4df3-a082-22c9ef82c8f5
-- title:
--   Verb: edit Ok children
-- statement:
--   The Verb construction uses the edit Ok children property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Agreement.lean#L579-L581
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Agreement.lean#L579-L581

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

theorem Nock.Verb.editOk_children {a l r} (h : editOk (.node a l r) = true) :
    editOk l = true ∧ editOk r = true := by sorry
