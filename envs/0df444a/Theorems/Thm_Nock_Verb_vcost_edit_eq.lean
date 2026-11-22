-- Prove2me | Theorems.Thm_Nock_Verb_vcost_edit_eq
-- name    : Nock.Verb.vcost_edit_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:05:46.023554+00:00
-- url     : https://prove2.me/theorems/01b6140c-9c92-4a3b-8f86-b58b0fbc84a4
-- title:
--   Verb: vcost edit eq
-- statement:
--   The Verb construction uses the vcost edit eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureComplete.lean#L135-L136
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureComplete.lean#L135-L136

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

theorem Nock.Verb.vcost_edit_eq {F : Nat} {l r : Verb} :
    vcost F (Verb.node .edit l r) = 1 + vcost F l + vcost F r := by sorry
