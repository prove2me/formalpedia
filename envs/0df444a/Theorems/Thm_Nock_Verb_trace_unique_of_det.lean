-- Prove2me | Theorems.Thm_Nock_Verb_trace_unique_of_det
-- name    : Nock.Verb.trace_unique_of_det
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:10:31.514794+00:00
-- url     : https://prove2.me/theorems/c275c14d-185d-40a7-beab-34ae0fa2833b
-- title:
--   Verb: trace unique of det
-- statement:
--   Trace uniqueness for **any deterministic** transition relation.  Determinism of the
--       relation is the only hypothesis; this is the inductive core shared by the functional and
--       the strict-order forms.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Trace.lean#L210-L246
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Trace.lean#L210-L246

module
public import Definitions.Def_LeanPool_PureNock_Verb
public import Batteries.Tactic.Alias
public import Definitions.Def_LeanPool_PureNock_Trace
set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb

theorem Nock.Verb.trace_unique_of_det {R : Verb → Verb → Prop}
    (hdet : ∀ {a b b' : Verb}, R a b → R a b' → b = b') :
    ∀ (T1 T2 : List Verb), ConsistentR R T1 → ConsistentR R T2 →
      T1.head? = T2.head? → T1.length = T2.length → T1 = T2 := by sorry
