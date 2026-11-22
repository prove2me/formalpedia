-- Prove2me | Theorems.Thm_Nock_Verb_vcostN_slot_eq
-- name    : Nock.Verb.vcostN_slot_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:05:55.164475+00:00
-- url     : https://prove2.me/theorems/18fead8c-8632-440d-bb6c-25cbdf70c7a3
-- title:
--   Verb: vcost N slot eq
-- statement:
--   The Verb construction uses the vcost N slot eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureCompleteHint.lean#L354-L355
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureCompleteHint.lean#L354-L355

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

theorem Nock.Verb.vcostN_slot_eq {F : Nat} {l r : Verb} :
    vcostN F (Verb.node .slot l r) = 1 + vcostN F l + vcostN F r := by sorry
