-- Prove2me | Theorems.Thm_Nock_Verb_progressN
-- name    : Nock.Verb.progressN
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:17:17.694581+00:00
-- url     : https://prove2.me/theorems/ad28dd57-7fd6-4885-a697-d9a6e7420b9b
-- title:
--   Verb: progress N
-- statement:
--   A `den`-defined, `editOk`, non-terminal verb has a `nextHint` successor.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureCompleteHint.lean#L1409-L1594
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureCompleteHint.lean#L1409-L1594

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

theorem Nock.Verb.progressN {v : Verb} {x : Noun} (hwf : editOk v = true) (hd : Den v x)
    (hnt : isTerminal v = false) : ∃ v', nextHint v = some v' := by sorry
