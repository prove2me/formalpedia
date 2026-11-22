-- Prove2me | Theorems.Thm_Nock_Verb_run_completeN
-- name    : Nock.Verb.run_completeN
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:17:20.96382+00:00
-- url     : https://prove2.me/theorems/3dcb350d-bc24-42e9-98ba-193eae8438e7
-- title:
--   Verb: run complete N
-- statement:
--   The Verb construction uses the run complete N property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureCompleteHint.lean#L1598-L1630
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureCompleteHint.lean#L1598-L1630

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

theorem Nock.Verb.run_completeN {v : Verb} {x : Noun} (hok : editOk v = true) (hv : Den v x) :
    ∃ N, runHint N v = some x := by sorry
