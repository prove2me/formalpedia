-- Prove2me | Theorems.Thm_Nock_Verb_run_completeP
-- name    : Nock.Verb.run_completeP
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:15:16.691803+00:00
-- url     : https://prove2.me/theorems/cdee137e-9d44-47da-aa50-bc950f2abf0a
-- title:
--   Verb: run complete P
-- statement:
--   The Verb construction uses the run complete P property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureComplete.lean#L1108-L1140
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureComplete.lean#L1108-L1140

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

theorem Nock.Verb.run_completeP {v : Verb} {x : Noun} (hok : editOk v = true) (hv : DenP v x) :
    ∃ N, run N v = some x := by sorry
