-- Prove2me | Theorems.Thm_Nock_Verb_paper_hint_separation
-- name    : Nock.Verb.paper_hint_separation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:22:54.425038+00:00
-- url     : https://prove2.me/theorems/96c1aea7-059c-4128-9261-3caec277388d
-- title:
--   Verb: paper hint separation
-- statement:
--   On `*[42 11 33 0 1]`, `runProgram` crashes at every fuel while `runHint` yields `42`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureAgreement.lean#L968-L971
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureAgreement.lean#L968-L971

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

theorem Nock.Verb.paper_hint_separation :
    (∀ fuel, runProgram fuel (Noun.atom 42) hintProgStatic = none)
    ∧ (∃ fuel, runHintProgram fuel (Noun.atom 42) hintProgStatic = some (Noun.atom 42)) := by sorry
