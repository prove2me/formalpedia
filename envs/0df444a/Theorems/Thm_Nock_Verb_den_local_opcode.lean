-- Prove2me | Theorems.Thm_Nock_Verb_den_local_opcode
-- name    : Nock.Verb.den_local_opcode
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:12:03.360579+00:00
-- url     : https://prove2.me/theorems/d8426012-5784-467e-babc-a9beeba948a7
-- title:
--   Verb: den local opcode
-- statement:
--   The Verb construction uses the den local opcode property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Agreement.lean#L845-L1037
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Agreement.lean#L845-L1037

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

theorem Nock.Verb.den_local_opcode {sub r₀ x} (hd : inOpcodeDomain sub = true) (hr : reduce sub = some r₀) :
    (Den sub x ↔ Den r₀ x) := by sorry
