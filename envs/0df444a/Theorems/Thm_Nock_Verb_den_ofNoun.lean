-- Prove2me | Theorems.Thm_Nock_Verb_den_ofNoun
-- name    : Nock.Verb.den_ofNoun
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:11:10.321247+00:00
-- url     : https://prove2.me/theorems/aa11e952-4657-47ba-b662-4859f377b378
-- title:
--   Verb: den of Noun
-- statement:
--   The Verb construction uses the den of Noun property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Agreement.lean#L88-L98
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Agreement.lean#L88-L98

module
public import Definitions.Def_LeanPool_PureNock_Verb
public import Definitions.Def_LeanPool_PureNock_Semantics
public import Definitions.Def_LeanPool_PureNock_Agreement
set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
open Noun

theorem Nock.Verb.den_ofNoun : ∀ (n : Noun) (fuel : Nat), n.size ≤ fuel → den fuel (ofNoun n) = some n := by sorry
