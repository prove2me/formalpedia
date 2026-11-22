-- Prove2me | Theorems.Thm_Nock_Verb_eval_crash_invalid
-- name    : Nock.Verb.eval_crash_invalid
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:06:40.499556+00:00
-- url     : https://prove2.me/theorems/330ef93d-1e4f-465c-89af-6fdbe24c67ba
-- title:
--   Verb: eval crash invalid
-- statement:
--   **Crash soundness (program-tied).**  A `crash` reported by `eval` for the program `v` means `v`
--       is `Invalid`: its evaluation trace is complete and ends at a stuck non-terminal — the paper's ⊥
--       (`main.tex:1124`).  Unlike a bare "some crashing verb exists", the witness is the trace *of
--       `v`*.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Trace.lean#L474-L502
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Trace.lean#L474-L502

module
public import Definitions.Def_LeanPool_PureNock_Verb
public import Batteries.Tactic.Alias
public import Definitions.Def_LeanPool_PureNock_Trace
set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb

theorem Nock.Verb.eval_crash_invalid {n : Nat} {v : Verb} (h : eval n v = .crash) : Invalid v := by sorry
