-- Prove2me | Theorems.Thm_Nock_Verb_editOk_reduce
-- name    : Nock.Verb.editOk_reduce
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:04:44.253935+00:00
-- url     : https://prove2.me/theorems/ea5b443a-c1df-4ff0-ac3e-24bfa9ac59bb
-- title:
--   Verb: edit Ok reduce
-- statement:
--   The Verb construction uses the edit Ok reduce property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Agreement.lean#L1165-L1264
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Agreement.lean#L1165-L1264

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

theorem Nock.Verb.editOk_reduce {sub r₀} (hr : reduce sub = some r₀) (hok : editOk sub = true) :
    editOk r₀ = true := by sorry
