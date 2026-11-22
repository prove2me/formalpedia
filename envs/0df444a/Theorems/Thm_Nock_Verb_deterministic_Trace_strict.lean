-- Prove2me | Theorems.Thm_Nock_Verb_deterministic_Trace_strict
-- name    : Nock.Verb.deterministic_Trace_strict
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:10:40.561088+00:00
-- url     : https://prove2.me/theorems/96199787-2fdb-40ec-afff-7995a3de785d
-- title:
--   Verb: deterministic Trace strict
-- statement:
--   **`Thm:deterministic_Trace`** (`main.tex:1156–1157`).
--       If `map` enforces a strict ordering on finite verbs, then for every finite verb `F` and
--       integer `n`, there exists at most one consistent evaluation trace of size `n` for `F`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Trace.lean#L278-L283
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Trace.lean#L278-L283

module
public import Definitions.Def_LeanPool_PureNock_Verb
public import Batteries.Tactic.Alias
public import Definitions.Def_LeanPool_PureNock_Trace
set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb

theorem Nock.Verb.deterministic_Trace_strict {F : Verb} {n : Nat} {T1 T2 : List Verb}
    (h1 : TraceOf F T1) (h2 : TraceOf F T2)
    (hn1 : T1.length = n + 1) (hn2 : T2.length = n + 1) : T1 = T2 := by sorry
