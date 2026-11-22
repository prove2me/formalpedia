-- Prove2me | Theorems.Thm_Nock_Verb_eval_crash_checked
-- name    : Nock.Verb.eval_crash_checked
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:20:06.174835+00:00
-- url     : https://prove2.me/theorems/e3843aef-9497-42a3-9bf4-d03490ad2f63
-- title:
--   Verb: eval crash checked
-- statement:
--   **The reported crash is a checked ⊥ (program-tied).**  A `crash` for `v` exhibits the trace of
--       `v` reaching a state `w` that genuinely `Crashes` and whose ⊥-edge is accepted by the two-verb
--       checker (`NockCheck w none = true`) — verifiability tied to the *evaluated* program.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Trace.lean#L521-L527
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Trace.lean#L521-L527

module
public import Definitions.Def_LeanPool_PureNock_Verb
public import Batteries.Tactic.Alias
public import Definitions.Def_LeanPool_PureNock_Trace
set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb

theorem Nock.Verb.eval_crash_checked {n : Nat} {v : Verb} (h : eval n v = .crash) :
    ∃ T w, TraceOf v T ∧ T.getLast? = some w ∧ Crashes w ∧ NockCheck w none = true := by sorry
