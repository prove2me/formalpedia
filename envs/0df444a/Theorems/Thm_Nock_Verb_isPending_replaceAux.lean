-- Prove2me | Theorems.Thm_Nock_Verb_isPending_replaceAux
-- name    : Nock.Verb.isPending_replaceAux
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:12:12.02812+00:00
-- url     : https://prove2.me/theorems/9e474928-4af3-441a-a189-c13c407fe0cf
-- title:
--   Verb: is Pending replace Aux
-- statement:
--   The Verb construction uses the is Pending replace Aux property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Agreement.lean#L1275-L1279
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Agreement.lean#L1275-L1279

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

theorem Nock.Verb.isPending_replaceAux (i : Nat) (r₀ : Verb) : ∀ (v : Verb) (c : Nat), c ≠ i →
    Verb.isPending (replaceAux i r₀ v c).2 = Verb.isPending v := by sorry
