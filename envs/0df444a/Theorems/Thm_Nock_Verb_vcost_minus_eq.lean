-- Prove2me | Theorems.Thm_Nock_Verb_vcost_minus_eq
-- name    : Nock.Verb.vcost_minus_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:05:38.882798+00:00
-- url     : https://prove2.me/theorems/f785db76-667f-4487-baa2-3744ee53e38f
-- title:
--   Verb: vcost minus eq
-- statement:
--   The Verb construction uses the vcost minus eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureComplete.lean#L133-L134
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureComplete.lean#L133-L134

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

theorem Nock.Verb.vcost_minus_eq {F : Nat} {l r : Verb} :
    vcost F (Verb.node .minus l r) = 1 + vcost F l + vcost F r := by sorry
