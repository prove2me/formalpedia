-- Prove2me | Theorems.Thm_Nock_Verb_runProgram_hint_crash
-- name    : Nock.Verb.runProgram_hint_crash
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:13:49.404805+00:00
-- url     : https://prove2.me/theorems/53a4fce9-e93f-43db-bc89-732d1cdcd52e
-- title:
--   Verb: run Program hint crash
-- statement:
--   **Paper machine crashes on hints (all fuel).**  For every fuel budget, `runProgram` of a
--       hint program `*[subj 11 …]` is `⊥`: the very first step crashes (OP₁₁ ∉ paper domain),
--       and the crashed root `*`-verb is not terminal, so `result` is `⊥`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureAgreement.lean#L947-L955
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureAgreement.lean#L947-L955

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

theorem Nock.Verb.runProgram_hint_crash (subj n2 : Noun) :
    ∀ fuel, runProgram fuel subj (.cell (.atom 11) n2) = none := by sorry
