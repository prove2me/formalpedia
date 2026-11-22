-- Prove2me | Theorems.Thm_Nock_Verb_traceOf_of_traceOfROM
-- name    : Nock.Verb.traceOf_of_traceOfROM
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:10:55.297474+00:00
-- url     : https://prove2.me/theorems/66eac810-fe36-4747-b551-ef7b8457d784
-- title:
--   Verb: trace Of of trace Of ROM
-- statement:
--   Every ROM trace of `F` is a Nock trace of `F`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Trace.lean#L397-L398
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Trace.lean#L397-L398

module
public import Definitions.Def_LeanPool_PureNock_Verb
public import Batteries.Tactic.Alias
public import Definitions.Def_LeanPool_PureNock_Trace
set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb

theorem Nock.Verb.traceOf_of_traceOfROM {F : Verb} {T : List Verb} (h : TraceOfROM F T) : TraceOf F T := by sorry
