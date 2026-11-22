-- Prove2me | Theorems.Thm_Nock_Verb_finite_of_validROM
-- name    : Nock.Verb.finite_of_validROM
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:19:49.181033+00:00
-- url     : https://prove2.me/theorems/bc17b427-6dce-4a41-922d-dc0efc77a65f
-- title:
--   Verb: finite of valid ROM
-- statement:
--   **ROM-valid ⇒ finite.**  A verb that terminates in a terminal state using only ROM steps
--       is Nock-finite: its ROM trace is a Nock trace (`traceOf_of_traceOfROM`), and its terminal
--       last verb has no Nock successor either (`next_none_of_terminal`), so the trace is
--       Nock-complete.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Trace.lean#L417-L419
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Trace.lean#L417-L419

module
public import Definitions.Def_LeanPool_PureNock_Verb
public import Batteries.Tactic.Alias
public import Definitions.Def_LeanPool_PureNock_Trace
set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb

theorem Nock.Verb.finite_of_validROM {F : Verb} (h : ValidROM F) : Finite F := by sorry
