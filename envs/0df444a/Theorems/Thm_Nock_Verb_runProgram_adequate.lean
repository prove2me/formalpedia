-- Prove2me | Theorems.Thm_Nock_Verb_runProgram_adequate
-- name    : Nock.Verb.runProgram_adequate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:14:27.704224+00:00
-- url     : https://prove2.me/theorems/5631f55d-5db6-4ad9-9129-411c7e618100
-- title:
--   Verb: run Program adequate
-- statement:
--   Conditional wrapper for OP₀–OP₁₀ consistency (see `runProgram_adequate_complete`).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureAgreement.lean#L1938-L1940
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureAgreement.lean#L1938-L1940

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

theorem Nock.Verb.runProgram_adequate (hc : PaperComplete) (s f r : Noun) :
    (∃ fuel, runProgram fuel s f = some r) ↔ (∃ fuel, evalPaper fuel s f = some r) := by sorry
