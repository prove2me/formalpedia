-- Prove2me | Theorems.Thm_Nock_Verb_replaceAux_rel
-- name    : Nock.Verb.replaceAux_rel
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:04:36.502945+00:00
-- url     : https://prove2.me/theorems/49988875-8fd5-4ec3-9226-d87b159112b7
-- title:
--   Verb: replace Aux rel
-- statement:
--   The Verb construction uses the replace Aux rel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Agreement.lean#L1063-L1101
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Agreement.lean#L1063-L1101

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

theorem Nock.Verb.replaceAux_rel (i : Nat) (r₀ : Verb) :
    ∀ (v : Verb) (c : Nat),
      (∀ sub, findAt i (enum v c).2 = some sub →
        sub.isPending = true ∧ (∀ x, Den sub x ↔ Den r₀ x)) →
      Rel v (replaceAux i r₀ v c).2 := by sorry
