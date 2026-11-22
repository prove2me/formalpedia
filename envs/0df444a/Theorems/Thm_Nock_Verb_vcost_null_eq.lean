-- Prove2me | Theorems.Thm_Nock_Verb_vcost_null_eq
-- name    : Nock.Verb.vcost_null_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:05:48.614431+00:00
-- url     : https://prove2.me/theorems/c85c70c3-5256-4313-8ab8-a21fb520dab9
-- title:
--   Verb: vcost null eq
-- statement:
--   The Verb construction uses the vcost null eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureComplete.lean#L137-L139
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureComplete.lean#L137-L139

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

theorem Nock.Verb.vcost_null_eq {F : Nat} {l r : Verb} :
    vcost F (Verb.node .null l r) = vcost F l + vcost F r := by sorry
