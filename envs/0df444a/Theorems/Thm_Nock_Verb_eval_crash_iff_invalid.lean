-- Prove2me | Theorems.Thm_Nock_Verb_eval_crash_iff_invalid
-- name    : Nock.Verb.eval_crash_iff_invalid
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:20:02.387966+00:00
-- url     : https://prove2.me/theorems/e66bf2a2-95a8-483a-98ea-ec41f598afd2
-- title:
--   Verb: eval crash iff invalid
-- statement:
--   **Verifiable crash ↔ ⊥.**  `eval` crashes on `v` (at some fuel) iff `v` is `Invalid` — the
--       clean soundness/completeness biconditional at the paper's ⊥ (`main.tex:1124`).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Trace.lean#L514-L515
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Trace.lean#L514-L515

module
public import Definitions.Def_LeanPool_PureNock_Verb
public import Batteries.Tactic.Alias
public import Definitions.Def_LeanPool_PureNock_Trace
set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb

theorem Nock.Verb.eval_crash_iff_invalid {v : Verb} : (∃ n, eval n v = .crash) ↔ Invalid v := by sorry
