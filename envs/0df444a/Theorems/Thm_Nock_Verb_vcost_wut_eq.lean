-- Prove2me | Theorems.Thm_Nock_Verb_vcost_wut_eq
-- name    : Nock.Verb.vcost_wut_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:14:46.420875+00:00
-- url     : https://prove2.me/theorems/d1da9a43-6042-4a50-9751-c3a1b974eae5
-- title:
--   Verb: vcost wut eq
-- statement:
--   The Verb construction uses the vcost wut eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureComplete.lean#L140-L142
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureComplete.lean#L140-L142

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

theorem Nock.Verb.vcost_wut_eq {F : Nat} {l r : Verb} :
    vcost F (Verb.node .wut l r) = vcost F l + vcost F r := by sorry
