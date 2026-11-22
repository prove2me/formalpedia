-- Prove2me | Theorems.Thm_Nock_Verb_den_term_children
-- name    : Nock.Verb.den_term_children
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:15:42.721527+00:00
-- url     : https://prove2.me/theorems/30887e31-0e2f-4bce-975c-5e90802d67de
-- title:
--   Verb: den term children
-- statement:
--   The Verb construction uses the den term children property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureCompleteHint.lean#L194-L201
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureCompleteHint.lean#L194-L201

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

theorem Nock.Verb.den_term_children {a : Action} {l r : Verb} {F : Nat} {x : Noun}
    (hok : editOk (Verb.node a l r) = true) (h : den F (Verb.node a l r) = some x)
    (htl : isTerminal l = true) (htr : isTerminal r = true) :
    den F l = some l.noun ∧ den F r = some r.noun := by sorry
