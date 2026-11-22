-- Prove2me | Theorems.Thm_Nock_Verb_denP_right_F
-- name    : Nock.Verb.denP_right_F
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:14:33.938819+00:00
-- url     : https://prove2.me/theorems/bb0078bd-0eef-4441-8c34-ea0055001cd3
-- title:
--   Verb: den P right F
-- statement:
--   The Verb construction uses the den P right F property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureComplete.lean#L28-L58
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureComplete.lean#L28-L58

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

theorem Nock.Verb.denP_right_F {a : Action} {l r : Verb} {f : Nat} {x : Noun}
    (hok : editOk (Verb.node a l r) = true) (h : denP (f + 1) (Verb.node a l r) = some x) :
    ∃ yr, denP (f + 1) r = some yr := by sorry
