-- Prove2me | Theorems.Thm_Nock_Verb_editOk_next
-- name    : Nock.Verb.editOk_next
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:04:50.935946+00:00
-- url     : https://prove2.me/theorems/885dc5bd-04b2-4a5d-824f-8aa4ad39f230
-- title:
--   Verb: edit Ok next
-- statement:
--   The Verb construction uses the edit Ok next property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Agreement.lean#L1364-L1374
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Agreement.lean#L1364-L1374

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

theorem Nock.Verb.editOk_next {v v'} (h : next v = some v') (hok : editOk v = true) : editOk v' = true := by sorry
