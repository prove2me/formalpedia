-- Prove2me | Theorems.Thm_Nock_Verb_editOk_replaceAux
-- name    : Nock.Verb.editOk_replaceAux
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:03:28.518607+00:00
-- url     : https://prove2.me/theorems/a993e7be-d62b-422d-8b5d-a181aabb41f4
-- title:
--   Verb: edit Ok replace Aux
-- statement:
--   The Verb construction uses the edit Ok replace Aux property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Agreement.lean#L1281-L1339
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Agreement.lean#L1281-L1339

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

theorem Nock.Verb.editOk_replaceAux (i : Nat) (r₀ : Verb) (hr0 : editOk r₀ = true) :
    ∀ (v : Verb) (c : Nat), editOk v = true →
      (∀ s, findAt i (enum v c).2 = some s → s.isPending = true) →
      editOk (replaceAux i r₀ v c).2 = true := by sorry
