-- Prove2me | Theorems.Thm_Nock_Verb_isTerminal_of_map_ofNoun
-- name    : Nock.Verb.isTerminal_of_map_ofNoun
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:08:42.078237+00:00
-- url     : https://prove2.me/theorems/4bfcc5be-1a4d-474c-be6a-6a7c81fc58ff
-- title:
--   Verb: is Terminal of map of Noun
-- statement:
--   The Verb construction uses the is Terminal of map of Noun property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureComplete.lean#L116-L118
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureComplete.lean#L116-L118

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

theorem Nock.Verb.isTerminal_of_map_ofNoun {o : Option Noun} {r₀ : Verb}
    (h : o.map ofNoun = some r₀) : isTerminal r₀ = true := by sorry
