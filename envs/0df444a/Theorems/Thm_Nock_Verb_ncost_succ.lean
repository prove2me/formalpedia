-- Prove2me | Theorems.Thm_Nock_Verb_ncost_succ
-- name    : Nock.Verb.ncost_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:08:58.43713+00:00
-- url     : https://prove2.me/theorems/403d267c-6cb0-41c7-935b-fd4282a0918c
-- title:
--   Verb: ncost succ
-- statement:
--   The Verb construction uses the ncost succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureCompleteHint.lean#L334-L339
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureCompleteHint.lean#L334-L339

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

theorem Nock.Verb.ncost_succ {n : Nat} {a b : Noun} {r : Noun}
    (hb : evalN n a b = some r) : ncost (n + 1) a b = ncost n a b := by sorry
