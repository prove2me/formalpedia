-- Prove2me | Theorems.Thm_Nock_Verb_evalProgram_hint_crash
-- name    : Nock.Verb.evalProgram_hint_crash
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:13:54.86638+00:00
-- url     : https://prove2.me/theorems/7368e1a6-280a-466a-ba75-d8f724698a37
-- title:
--   Verb: eval Program hint crash
-- statement:
--   **Positive verifiable crash.**  A `*[subj 11 …]` program — a non-opcode head atom `11`
--       (`11 ∉ [11] = {0,…,10}`, `main.tex:1052,1083`), outside the paper's opcode domain — reports
--       `Outcome.crash` under `eval`, not merely `none` under `run`: the first step is stuck
--       (`next_hintProg_none`) and the crashed `*`-root is non-terminal, so `haltOutcome` is
--       `crash`.  By
--       `eval_crash_invalid` the evaluated program is `Invalid` (the paper's ⊥, `main.tex:1124`),
--       not fuel
--       exhaustion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureAgreement.lean#L981-L985
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureAgreement.lean#L981-L985

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

theorem Nock.Verb.evalProgram_hint_crash (subj n2 : Noun) :
    evalProgram 1 subj (.cell (.atom 11) n2) = .crash := by sorry
