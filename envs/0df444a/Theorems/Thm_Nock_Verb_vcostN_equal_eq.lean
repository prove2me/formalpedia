-- Prove2me | Theorems.Thm_Nock_Verb_vcostN_equal_eq
-- name    : Nock.Verb.vcostN_equal_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:06:00.892724+00:00
-- url     : https://prove2.me/theorems/41dda073-2bb9-4f75-8f21-196db7e6ac40
-- title:
--   Verb: vcost N equal eq
-- statement:
--   The Verb construction uses the vcost N equal eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureCompleteHint.lean#L356-L357
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureCompleteHint.lean#L356-L357

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

theorem Nock.Verb.vcostN_equal_eq {F : Nat} {l r : Verb} :
    vcostN F (Verb.node .equal l r) = 1 + vcostN F l + vcostN F r := by sorry
