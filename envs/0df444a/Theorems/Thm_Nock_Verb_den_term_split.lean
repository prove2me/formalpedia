-- Prove2me | Theorems.Thm_Nock_Verb_den_term_split
-- name    : Nock.Verb.den_term_split
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:15:46.202979+00:00
-- url     : https://prove2.me/theorems/b928bcca-6d79-4869-8d0b-bb307d5dc240
-- title:
--   Verb: den term split
-- statement:
--   The Verb construction uses the den term split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureCompleteHint.lean#L203-L216
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureCompleteHint.lean#L203-L216

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

theorem Nock.Verb.den_term_split {l r : Verb} {f : Nat} {x : Noun}
    (htl : isTerminal l = true) (htr : isTerminal r = true)
    (h : den (f + 1) (Verb.node .null l r) = some x) :
    den f l = some l.noun ∧ den f r = some r.noun := by sorry
