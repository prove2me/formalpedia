-- Prove2me | Theorems.Thm_Nock_Verb_selStep_deterministic_Trace
-- name    : Nock.Verb.selStep_deterministic_Trace
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:10:33.520863+00:00
-- url     : https://prove2.me/theorems/b6be62fc-f217-40db-b6e4-24da3d9fad89
-- title:
--   Verb: sel Step deterministic Trace
-- statement:
--   **`Thm:deterministic_Trace`** (`main.tex:1156–1157`).
--       If `map` enforces a strict ordering on finite verbs, then for every finite verb `F` and
--       integer `n`, there exists at most one consistent evaluation trace of size `n` for `F`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Trace.lean#L256-L262
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Trace.lean#L256-L262

module
public import Definitions.Def_LeanPool_PureNock_Verb
public import Batteries.Tactic.Alias
public import Definitions.Def_LeanPool_PureNock_Trace
set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb

theorem Nock.Verb.selStep_deterministic_Trace {lt : Nat → Nat → Prop} (hs : StrictSelect lt)
    {F : Verb} {n : Nat} {T1 T2 : List Verb}
    (h1 : TraceOfR (SelStep lt) F T1) (h2 : TraceOfR (SelStep lt) F T2)
    (hn1 : T1.length = n + 1) (hn2 : T2.length = n + 1) : T1 = T2 := by sorry
