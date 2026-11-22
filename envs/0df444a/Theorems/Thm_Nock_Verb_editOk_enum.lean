-- Prove2me | Theorems.Thm_Nock_Verb_editOk_enum
-- name    : Nock.Verb.editOk_enum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:03:32.512903+00:00
-- url     : https://prove2.me/theorems/6ad5cf22-51a8-4d9c-bfee-3a7fe414bce6
-- title:
--   Verb: edit Ok enum
-- statement:
--   The Verb construction uses the edit Ok enum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Agreement.lean#L1341-L1353
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Agreement.lean#L1341-L1353

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

theorem Nock.Verb.editOk_enum : ∀ (v : Verb) (c : Nat), editOk v = true →
    ∀ p ∈ (enum v c).2, editOk p.2 = true := by sorry
