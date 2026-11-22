-- Prove2me | Theorems.Thm_Nock_Verb_den_local
-- name    : Nock.Verb.den_local
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:07:27.607854+00:00
-- url     : https://prove2.me/theorems/803871b3-4c09-444a-938a-bec9532079c2
-- title:
--   Verb: den local
-- statement:
--   The Verb construction uses the den local property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Agreement.lean#L1357-L1362
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Agreement.lean#L1357-L1362

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

theorem Nock.Verb.den_local {sub r₀ x} (hd : inDomain sub = true) (hr : reduce sub = some r₀) :
    (Den sub x ↔ Den r₀ x) := by sorry
