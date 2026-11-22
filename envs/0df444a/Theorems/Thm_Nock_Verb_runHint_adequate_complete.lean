-- Prove2me | Theorems.Thm_Nock_Verb_runHint_adequate_complete
-- name    : Nock.Verb.runHint_adequate_complete
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:17:21.82594+00:00
-- url     : https://prove2.me/theorems/f7daed76-1017-4cf7-aa0c-522cbca72dde
-- title:
--   Verb: run Hint adequate complete
-- statement:
--   The Verb construction uses the run Hint adequate complete property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureCompleteHint.lean#L1640-L1642
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureCompleteHint.lean#L1640-L1642

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

theorem Nock.Verb.runHint_adequate_complete (s f r : Noun) :
    (∃ fuel, runHintProgram fuel s f = some r) ↔ (∃ fuel, evalN fuel s f = some r) := by sorry
