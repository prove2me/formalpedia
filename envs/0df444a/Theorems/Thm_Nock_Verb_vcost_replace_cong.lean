-- Prove2me | Theorems.Thm_Nock_Verb_vcost_replace_cong
-- name    : Nock.Verb.vcost_replace_cong
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:15:15.998802+00:00
-- url     : https://prove2.me/theorems/b16d429a-fdf5-4a7e-8f93-0bdcdec7fc9b
-- title:
--   Verb: vcost replace cong
-- statement:
--   **Step congruence for `vcost`.**  Swapping the (denotation-preserving, pending) subnode `sub`
--       for `r₀` changes `vcost F` by exactly `vcost F r₀ - vcost F sub` (additive form).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureComplete.lean#L956-L1037
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureComplete.lean#L956-L1037

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

theorem Nock.Verb.vcost_replace_cong (F i : Nat) (sub r₀ : Verb) (hpend : sub.isPending = true)
    (hgraph : ∀ y, DenP sub y ↔ DenP r₀ y) (hr0 : editOk r₀ = true) :
    ∀ (v : Verb) (c : Nat) (xv xv' : Noun),
      editOk v = true →
      findAt i (enum v c).2 = some sub →
      denP F v = some xv →
      denP F (replaceAux i r₀ v c).2 = some xv' →
      vcost F (replaceAux i r₀ v c).2 + vcost F sub = vcost F v + vcost F r₀ := by sorry
