-- Prove2me | Theorems.Thm_Nock_Verb_vcostN_wut_eq
-- name    : Nock.Verb.vcostN_wut_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:15:59.752592+00:00
-- url     : https://prove2.me/theorems/4f112375-d6d9-417b-8ada-82843ecb1f75
-- title:
--   Verb: vcost N wut eq
-- statement:
--   The Verb construction uses the vcost N wut eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureCompleteHint.lean#L365-L367
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureCompleteHint.lean#L365-L367

module
public import Definitions.Def_LeanPool_PureNock_PureComplete
public import Mathlib.Tactic.IntervalCases
public import Definitions.Def_LeanPool_PureNock_PureCompleteHint
set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
open Noun

theorem Nock.Verb.vcostN_wut_eq {F : Nat} {l r : Verb} :
    vcostN F (Verb.node .wut l r) = vcostN F l + vcostN F r := by sorry
