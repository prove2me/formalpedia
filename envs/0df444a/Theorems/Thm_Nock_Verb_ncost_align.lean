-- Prove2me | Theorems.Thm_Nock_Verb_ncost_align
-- name    : Nock.Verb.ncost_align
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:09:13.202898+00:00
-- url     : https://prove2.me/theorems/57f3d645-f7b8-41cc-b360-4b05957379aa
-- title:
--   Verb: ncost align
-- statement:
--   The Verb construction uses the ncost align property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureCompleteHint.lean#L347-L349
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureCompleteHint.lean#L347-L349

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

theorem Nock.Verb.ncost_align {n m k : Nat} {a b r : Noun} (h : evalN n a b = some r)
    (hm : n ≤ m) (hk : n ≤ k) : ncost m a b = ncost k a b := by sorry
