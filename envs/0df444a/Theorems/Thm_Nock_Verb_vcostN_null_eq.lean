-- Prove2me | Theorems.Thm_Nock_Verb_vcostN_null_eq
-- name    : Nock.Verb.vcostN_null_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:06:04.950084+00:00
-- url     : https://prove2.me/theorems/18159608-d0ba-42a1-82df-27ed4a363665
-- title:
--   Verb: vcost N null eq
-- statement:
--   The Verb construction uses the vcost N null eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureCompleteHint.lean#L362-L364
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureCompleteHint.lean#L362-L364

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

theorem Nock.Verb.vcostN_null_eq {F : Nat} {l r : Verb} :
    vcostN F (Verb.node .null l r) = vcostN F l + vcostN F r := by sorry
