-- Prove2me | Theorems.Thm_Nock_Verb_vcost_star_eq
-- name    : Nock.Verb.vcost_star_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:03:59.280167+00:00
-- url     : https://prove2.me/theorems/e47fda2d-9afb-4ba5-8c0b-b7475414b903
-- title:
--   Verb: vcost star eq
-- statement:
--   The Verb construction uses the vcost star eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureComplete.lean#L126-L128
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureComplete.lean#L126-L128

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

theorem Nock.Verb.vcost_star_eq {F : Nat} {l r : Verb} : vcost F (Verb.node .star l r) =
    (match denP F l, denP F r with | some sa, some fo => pcost F sa fo | _, _ => 0)
      + vcost F l + vcost F r := by sorry
