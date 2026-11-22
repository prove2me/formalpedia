-- Prove2me | Theorems.Thm_Nock_Verb_next_of_nextROM
-- name    : Nock.Verb.next_of_nextROM
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:10:16.611771+00:00
-- url     : https://prove2.me/theorems/adbb072d-c6d1-4d30-a9ac-dc227c151691
-- title:
--   Verb: next of next ROM
-- statement:
--   **Every ROM transition is a Nock transition.**  `nextROM` is a *restriction* of `next`
--       (`OP₁₀` removed): if `nextROM v = some w` then `next v = some w`.  This is the verb-level
--       sense in which `NockVMROM` is `NockVM` without `OP₁₀`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Verb.lean#L874-L893
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Verb.lean#L874-L893

module
public import Definitions.Def_LeanPool_PureNock_Tree
public import Definitions.Def_LeanPool_PureNock_Reference
public import Definitions.Def_LeanPool_PureNock_Verb
set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb

theorem Nock.Verb.next_of_nextROM {v w : Verb} (h : nextROM v = some w) : next v = some w := by sorry
