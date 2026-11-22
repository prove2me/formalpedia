-- Prove2me | Theorems.Thm_Nock_Verb_trace_unique
-- name    : Nock.Verb.trace_unique
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:10:29.626186+00:00
-- url     : https://prove2.me/theorems/c8802fef-c2dc-4204-b73e-baf0bd69717a
-- title:
--   Verb: trace unique
-- statement:
--   Inductive core of determinism: `Step` is functional, so equal heads and lengths force equality.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Trace.lean#L154-L187
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Trace.lean#L154-L187

module
public import Definitions.Def_LeanPool_PureNock_Verb
public import Batteries.Tactic.Alias
public import Definitions.Def_LeanPool_PureNock_Trace
set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb

theorem Nock.Verb.trace_unique (T1 : List Verb) : ∀ (T2 : List Verb),
    Consistent T1 → Consistent T2 → T1.head? = T2.head? → T1.length = T2.length → T1 = T2 := by sorry
