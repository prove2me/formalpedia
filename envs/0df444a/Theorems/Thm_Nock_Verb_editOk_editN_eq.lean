-- Prove2me | Theorems.Thm_Nock_Verb_editOk_editN_eq
-- name    : Nock.Verb.editOk_editN_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:12:06.451496+00:00
-- url     : https://prove2.me/theorems/1ef1aa1b-f6cc-4256-897a-771ac2e7eca3
-- title:
--   Verb: edit Ok edit N eq
-- statement:
--   The Verb construction uses the edit Ok edit N eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Agreement.lean#L1272-L1273
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Agreement.lean#L1272-L1273

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

theorem Nock.Verb.editOk_editN_eq {l r} : editOk (.node .edit l r) = (!Verb.isPending r && editOk l && editOk
  r) := by sorry
