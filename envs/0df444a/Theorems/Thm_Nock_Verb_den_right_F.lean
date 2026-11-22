-- Prove2me | Theorems.Thm_Nock_Verb_den_right_F
-- name    : Nock.Verb.den_right_F
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:15:41.303833+00:00
-- url     : https://prove2.me/theorems/72bd69e2-0995-4777-ab6e-979dca2ce918
-- title:
--   Verb: den right F
-- statement:
--   The Verb construction uses the den right F property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureCompleteHint.lean#L137-L177
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureCompleteHint.lean#L137-L177

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

theorem Nock.Verb.den_right_F {a : Action} {l r : Verb} {f : Nat} {x : Noun}
    (hok : editOk (Verb.node a l r) = true) (h : den (f + 1) (Verb.node a l r) = some x) :
    ∃ yr, den (f + 1) r = some yr := by sorry
