-- Prove2me | Theorems.Thm_Nock_Verb_replaceAux_notMem
-- name    : Nock.Verb.replaceAux_notMem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:08:54.454839+00:00
-- url     : https://prove2.me/theorems/bbeb9fdf-b429-4d82-8936-2cb509dd5c7c
-- title:
--   Verb: replace Aux not Mem
-- statement:
--   The Verb construction uses the replace Aux not Mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureComplete.lean#L926-L947
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureComplete.lean#L926-L947

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

theorem Nock.Verb.replaceAux_notMem (i : Nat) (r₀ : Verb) : ∀ (v : Verb) (c : Nat),
    findAt i (enum v c).2 = none → (replaceAux i r₀ v c).2 = v := by sorry
