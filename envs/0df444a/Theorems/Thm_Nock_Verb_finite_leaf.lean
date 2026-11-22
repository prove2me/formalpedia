-- Prove2me | Theorems.Thm_Nock_Verb_finite_leaf
-- name    : Nock.Verb.finite_leaf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:10:50.190846+00:00
-- url     : https://prove2.me/theorems/fbae7094-67b6-4a9f-a7b5-edc9e9bc4ac4
-- title:
--   Verb: finite leaf
-- statement:
--   A terminal leaf is finite: its one-element trace `[leaf n]` is complete.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Trace.lean#L352-L353
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Trace.lean#L352-L353

module
public import Definitions.Def_LeanPool_PureNock_Verb
public import Batteries.Tactic.Alias
public import Definitions.Def_LeanPool_PureNock_Trace
set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb

theorem Nock.Verb.finite_leaf (n : Nat) : Finite (.leaf n) := by sorry
