-- Prove2me | Theorems.Thm_Nock_Verb_editOk_null_eq
-- name    : Nock.Verb.editOk_null_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:04:31.161825+00:00
-- url     : https://prove2.me/theorems/1c93d2b2-e12b-44fe-8ee1-058c6443745e
-- title:
--   Verb: edit Ok null eq
-- statement:
--   The Verb construction uses the edit Ok null eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Agreement.lean#L576-L576
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Agreement.lean#L576-L576

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

theorem Nock.Verb.editOk_null_eq {l r} : editOk (.node .null l r) = (editOk l && editOk r) := by sorry
