-- Prove2me | Theorems.Thm_Nock_Verb_vcostN_replace_cong
-- name    : Nock.Verb.vcostN_replace_cong
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:16:14.722045+00:00
-- url     : https://prove2.me/theorems/9d21e886-4721-4c95-b6d1-c286be2d7cee
-- title:
--   Verb: vcost N replace cong
-- statement:
--   The Verb construction uses the vcost N replace cong property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureCompleteHint.lean#L1257-L1333
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureCompleteHint.lean#L1257-L1333

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

theorem Nock.Verb.vcostN_replace_cong (F i : Nat) (sub r₀ : Verb) (hpend : sub.isPending = true)
    (hgraph : ∀ y, Den sub y ↔ Den r₀ y) (hr0 : editOk r₀ = true) :
    ∀ (v : Verb) (c : Nat) (xv xv' : Noun),
      editOk v = true →
      findAt i (enum v c).2 = some sub →
      den F v = some xv →
      den F (replaceAux i r₀ v c).2 = some xv' →
      vcostN F (replaceAux i r₀ v c).2 + vcostN F sub = vcostN F v + vcostN F r₀ := by sorry
