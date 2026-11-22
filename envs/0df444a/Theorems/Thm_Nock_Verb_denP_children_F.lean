-- Prove2me | Theorems.Thm_Nock_Verb_denP_children_F
-- name    : Nock.Verb.denP_children_F
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:03:57.162342+00:00
-- url     : https://prove2.me/theorems/bffc941e-0fc7-4c87-aa1b-15fcd3e390ff
-- title:
--   Verb: den P children F
-- statement:
--   The Verb construction uses the den P children F property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureComplete.lean#L60-L69
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureComplete.lean#L60-L69

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

theorem Nock.Verb.denP_children_F {a : Action} {l r : Verb} {F : Nat} {x : Noun}
    (hok : editOk (Verb.node a l r) = true) (h : denP F (Verb.node a l r) = some x) :
    (∃ yl, denP F l = some yl) ∧ (∃ yr, denP F r = some yr) := by sorry
