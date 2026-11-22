-- Prove2me | Theorems.Thm_Nock_Verb_crash_of_trace
-- name    : Nock.Verb.crash_of_trace
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:10:55.502595+00:00
-- url     : https://prove2.me/theorems/9bda7e79-181d-4cc0-9177-aae05afda82a
-- title:
--   Verb: crash of trace
-- statement:
--   If `S` is a consistent trace of `u` (head `u`, `Consistent S`) whose last state `w` is a stuck
--       non-terminal (`next w = none`, `¬terminal`), then `eval` reports a `crash` at fuel
--       `S.length`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Trace.lean#L447-L467
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Trace.lean#L447-L467

module
public import Definitions.Def_LeanPool_PureNock_Verb
public import Batteries.Tactic.Alias
public import Definitions.Def_LeanPool_PureNock_Trace
set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb

theorem Nock.Verb.crash_of_trace :
    ∀ (S : List Verb) (u w : Verb),
      S.head? = some u → Consistent S → S.getLast? = some w →
      next w = none → isTerminal w = false → eval S.length u = .crash
  := by sorry
