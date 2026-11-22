-- Prove2me | Theorems.Thm_Nock_Verb_vcostN_minus_eq
-- name    : Nock.Verb.vcostN_minus_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:06:04.95526+00:00
-- url     : https://prove2.me/theorems/96418390-a278-4c21-99ca-a2b452765cf0
-- title:
--   Verb: vcost N minus eq
-- statement:
--   The Verb construction uses the vcost N minus eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureCompleteHint.lean#L358-L359
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureCompleteHint.lean#L358-L359

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

theorem Nock.Verb.vcostN_minus_eq {F : Nat} {l r : Verb} :
    vcostN F (Verb.node .minus l r) = 1 + vcostN F l + vcostN F r := by sorry
