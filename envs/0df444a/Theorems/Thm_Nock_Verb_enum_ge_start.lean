-- Prove2me | Theorems.Thm_Nock_Verb_enum_ge_start
-- name    : Nock.Verb.enum_ge_start
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:04:05.896042+00:00
-- url     : https://prove2.me/theorems/6b1ce053-e67e-4852-b89c-6984ca08bb16
-- title:
--   Verb: enum ge start
-- statement:
--   The DFS counter never decreases: `(enum v c).1 ≥ c`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Verb.lean#L334-L341
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Verb.lean#L334-L341

module
public import Definitions.Def_LeanPool_PureNock_Tree
public import Definitions.Def_LeanPool_PureNock_Reference
public import Definitions.Def_LeanPool_PureNock_Verb
set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb

theorem Nock.Verb.enum_ge_start (v : Verb) (c : Nat) : c ≤ (enum v c).1 := by sorry
