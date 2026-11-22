-- Prove2me | Theorems.Thm_Nock_Verb_vcost_equal_eq
-- name    : Nock.Verb.vcost_equal_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:05:36.43024+00:00
-- url     : https://prove2.me/theorems/46c6e816-b656-480e-9b15-d78dcb8e9e08
-- title:
--   Verb: vcost equal eq
-- statement:
--   The Verb construction uses the vcost equal eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureComplete.lean#L131-L132
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureComplete.lean#L131-L132

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

theorem Nock.Verb.vcost_equal_eq {F : Nat} {l r : Verb} :
    vcost F (Verb.node .equal l r) = 1 + vcost F l + vcost F r := by sorry
