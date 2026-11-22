-- Prove2me | Theorems.Thm_Nock_Verb_denP_term_children
-- name    : Nock.Verb.denP_term_children
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:14:39.532974+00:00
-- url     : https://prove2.me/theorems/f417f86b-099a-4788-bbaa-23c721683468
-- title:
--   Verb: den P term children
-- statement:
--   The Verb construction uses the den P term children property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureComplete.lean#L78-L85
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureComplete.lean#L78-L85

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

theorem Nock.Verb.denP_term_children {a : Action} {l r : Verb} {F : Nat} {x : Noun}
    (hok : editOk (Verb.node a l r) = true) (h : denP F (Verb.node a l r) = some x)
    (htl : isTerminal l = true) (htr : isTerminal r = true) :
    denP F l = some l.noun ∧ denP F r = some r.noun := by sorry
