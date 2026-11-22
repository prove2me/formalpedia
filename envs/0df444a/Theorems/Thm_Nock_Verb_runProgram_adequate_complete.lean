-- Prove2me | Theorems.Thm_Nock_Verb_runProgram_adequate_complete
-- name    : Nock.Verb.runProgram_adequate_complete
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:05:54.777078+00:00
-- url     : https://prove2.me/theorems/0d0b2440-c910-4f44-afc1-673786b5ea30
-- title:
--   Verb: run Program adequate complete
-- statement:
--   The paper-derived local machine and derived OP₀–OP₁₀ oracle compute the
--       same partial function. This is a Lean consistency theorem, not a theorem
--       stated in `main.tex`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureComplete.lean#L1156-L1158
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureComplete.lean#L1156-L1158

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

theorem Nock.Verb.runProgram_adequate_complete (s f r : Noun) :
    (∃ fuel, runProgram fuel s f = some r) ↔ (∃ fuel, evalPaper fuel s f = some r) := by sorry
