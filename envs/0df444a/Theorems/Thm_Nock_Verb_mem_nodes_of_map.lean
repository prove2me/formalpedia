-- Prove2me | Theorems.Thm_Nock_Verb_mem_nodes_of_map
-- name    : Nock.Verb.mem_nodes_of_map
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:00:12.777631+00:00
-- url     : https://prove2.me/theorems/11417ab6-18ea-467d-a2a2-027e22c61755
-- title:
--   Verb: mem nodes of map
-- statement:
--   Membership of the retrieved node: `map i a = some v ⇒ (i, v) ∈ nodes a`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Verb.lean#L440-L442
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Verb.lean#L440-L442

module
public import Definitions.Def_LeanPool_PureNock_Tree
public import Definitions.Def_LeanPool_PureNock_Reference
public import Definitions.Def_LeanPool_PureNock_Verb
set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb

theorem Nock.Verb.mem_nodes_of_map {a : Verb} {i : Nat} {v : Verb}
    (h : map i a = some v) : (i, v) ∈ nodes a := by sorry
