-- Prove2me | Theorems.Thm_Nock_Verb_paper_hint_separation_crash
-- name    : Nock.Verb.paper_hint_separation_crash
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:22:57.899706+00:00
-- url     : https://prove2.me/theorems/e69faff8-69e5-441c-97c3-44ffcce6ab85
-- title:
--   Verb: paper hint separation crash
-- statement:
--   Sharpened separation: `eval` reports a positive `crash` on the non-opcode-head program while
--       `runHint` yields `42` — "provably crashes", not just "produces no value".
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureAgreement.lean#L989-L992
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureAgreement.lean#L989-L992

module
public import Definitions.Def_LeanPool_PureNock_Agreement
public import Definitions.Def_LeanPool_PureNock_Trace
public import Definitions.Def_LeanPool_PureNock_PaperReference
public import Mathlib.Tactic.IntervalCases
public import Definitions.Def_LeanPool_PureNock_PureAgreement
set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
open Noun

theorem Nock.Verb.paper_hint_separation_crash :
    evalProgram 1 (Noun.atom 42) hintProgStatic = .crash
    ∧ (∃ fuel, runHintProgram fuel (Noun.atom 42) hintProgStatic = some (Noun.atom 42)) := by sorry
