-- Prove2me | Theorems.Thm_Nock_Verb_den_children_F
-- name    : Nock.Verb.den_children_F
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:03:56.396299+00:00
-- url     : https://prove2.me/theorems/96097cba-f1c5-447a-9ec5-351767174e3b
-- title:
--   Verb: den children F
-- statement:
--   The Verb construction uses the den children F property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureCompleteHint.lean#L179-L188
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureCompleteHint.lean#L179-L188

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

theorem Nock.Verb.den_children_F {a : Action} {l r : Verb} {F : Nat} {x : Noun}
    (hok : editOk (Verb.node a l r) = true) (h : den F (Verb.node a l r) = some x) :
    (∃ yl, den F l = some yl) ∧ (∃ yr, den F r = some yr) := by sorry
