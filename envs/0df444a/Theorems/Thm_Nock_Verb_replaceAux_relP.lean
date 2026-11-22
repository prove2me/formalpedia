-- Prove2me | Theorems.Thm_Nock_Verb_replaceAux_relP
-- name    : Nock.Verb.replaceAux_relP
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:08:22.465707+00:00
-- url     : https://prove2.me/theorems/2636074d-875d-439c-b923-dd7cfa3af718
-- title:
--   Verb: replace Aux rel P
-- statement:
--   The Verb construction uses the replace Aux rel P property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureAgreement.lean#L1414-L1452
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureAgreement.lean#L1414-L1452

module
public import Definitions.Def_LeanPool_PureNock_Agreement
public import Definitions.Def_LeanPool_PureNock_Trace
public import Definitions.Def_LeanPool_PureNock_PaperReference
public import Mathlib.Tactic.IntervalCases
public import Definitions.Def_LeanPool_PureNock_PureAgreement
set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
open Noun

theorem Nock.Verb.replaceAux_relP (i : Nat) (r₀ : Verb) :
    ∀ (v : Verb) (c : Nat),
      (∀ sub, findAt i (enum v c).2 = some sub →
        sub.isPending = true ∧ (∀ x, DenP sub x ↔ DenP r₀ x)) →
      RelP v (replaceAux i r₀ v c).2 := by sorry
