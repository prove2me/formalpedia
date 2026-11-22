-- Prove2me | Theorems.Thm_Nock_Verb_vcostN_terminal
-- name    : Nock.Verb.vcostN_terminal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:04:10.195993+00:00
-- url     : https://prove2.me/theorems/d2c5c420-46a2-401b-9590-04802b029bc8
-- title:
--   Verb: vcost N terminal
-- statement:
--   The Verb construction uses the vcost N terminal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureCompleteHint.lean#L369-L379
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureCompleteHint.lean#L369-L379

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

theorem Nock.Verb.vcostN_terminal : ∀ (v : Verb), isTerminal v = true → ∀ F, vcostN F v = 0 := by sorry
