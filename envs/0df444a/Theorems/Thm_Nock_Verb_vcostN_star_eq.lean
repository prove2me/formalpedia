-- Prove2me | Theorems.Thm_Nock_Verb_vcostN_star_eq
-- name    : Nock.Verb.vcostN_star_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:04:02.99992+00:00
-- url     : https://prove2.me/theorems/584aef97-8c5b-4854-9c50-45243728f543
-- title:
--   Verb: vcost N star eq
-- statement:
--   The Verb construction uses the vcost N star eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureCompleteHint.lean#L351-L353
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureCompleteHint.lean#L351-L353

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

theorem Nock.Verb.vcostN_star_eq {F : Nat} {l r : Verb} : vcostN F (Verb.node .star l r) =
    (match den F l, den F r with | some sa, some fo => ncost F sa fo | _, _ => 0)
      + vcostN F l + vcostN F r := by sorry
