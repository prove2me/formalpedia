-- Prove2me | Theorems.Thm_Nock_Verb_den_pair
-- name    : Nock.Verb.den_pair
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:02:10.829664+00:00
-- url     : https://prove2.me/theorems/5c503078-5c0b-46d4-bec5-a5b6c67bc738
-- title:
--   Verb: den pair
-- statement:
--   The Verb construction uses the den pair property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Agreement.lean#L152-L155
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Agreement.lean#L152-L155

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

theorem Nock.Verb.den_pair {l r a b} (hl : Den l a) (hr : Den r b) :
    ∃ f, den f l = some a ∧ den f r = some b := by sorry
