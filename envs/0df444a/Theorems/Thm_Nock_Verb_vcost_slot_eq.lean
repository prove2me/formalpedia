-- Prove2me | Theorems.Thm_Nock_Verb_vcost_slot_eq
-- name    : Nock.Verb.vcost_slot_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:05:31.815667+00:00
-- url     : https://prove2.me/theorems/bfb3c6f6-6b13-4dab-a3cc-878652b983c4
-- title:
--   Verb: vcost slot eq
-- statement:
--   The Verb construction uses the vcost slot eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureComplete.lean#L129-L130
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureComplete.lean#L129-L130

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

theorem Nock.Verb.vcost_slot_eq {F : Nat} {l r : Verb} :
    vcost F (Verb.node .slot l r) = 1 + vcost F l + vcost F r := by sorry
