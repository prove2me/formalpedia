-- Prove2me | Theorems.Thm_Nock_Verb_consistent_iff_selStep
-- name    : Nock.Verb.consistent_iff_selStep
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:10:35.92258+00:00
-- url     : https://prove2.me/theorems/5e2f7011-eeef-444f-94cc-47d12138cc96
-- title:
--   Verb: consistent iff sel Step
-- statement:
--   The concrete consistency (`Consistent`, via `next`) is exactly `SelStep dfsLt`
--       consistency, because `next` realizes the DFS selection step (`next_eq_some_iff`).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Trace.lean#L266-L272
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Trace.lean#L266-L272

module
public import Definitions.Def_LeanPool_PureNock_Verb
public import Batteries.Tactic.Alias
public import Definitions.Def_LeanPool_PureNock_Trace
set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb

theorem Nock.Verb.consistent_iff_selStep : ∀ (T : List Verb),
    Consistent T ↔ ConsistentR (SelStep dfsLt) T
  := by sorry
