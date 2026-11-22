-- Prove2me | Theorems.Thm_Nock_Verb_vcost_mono
-- name    : Nock.Verb.vcost_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:14:53.362853+00:00
-- url     : https://prove2.me/theorems/274fddec-f1f6-4c8d-b0f4-8074e07fd00e
-- title:
--   Verb: vcost mono
-- statement:
--   The Verb construction uses the vcost mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureComplete.lean#L195-L199
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureComplete.lean#L195-L199

module
public import Definitions.Def_LeanPool_PureNock_PureAgreement
public import Mathlib.Tactic.IntervalCases
public import Definitions.Def_LeanPool_PureNock_PureComplete
set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
open Noun

theorem Nock.Verb.vcost_mono {F G : Nat} {v : Verb} {x : Noun}
    (hle : F ≤ G) (hok : editOk v = true) (hv : denP F v = some x) : vcost G v = vcost F v := by sorry
