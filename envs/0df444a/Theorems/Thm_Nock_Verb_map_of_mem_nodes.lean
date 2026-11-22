-- Prove2me | Theorems.Thm_Nock_Verb_map_of_mem_nodes
-- name    : Nock.Verb.map_of_mem_nodes
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:10:08.368073+00:00
-- url     : https://prove2.me/theorems/d4739640-f1f4-43ba-ae66-5a789c6805b3
-- title:
--   Verb: map of mem nodes
-- statement:
--   **`map` retrieves the unique node at an index.**  If `(i, v)` is one of the DFS
--       internal-node pairs of `a`, then `map i a = some v`.  (Uses DFS distinctness,
--       `enum_findAt`.)
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Verb.lean#L435-L437
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Verb.lean#L435-L437

module
public import Definitions.Def_LeanPool_PureNock_Tree
public import Definitions.Def_LeanPool_PureNock_Reference
public import Definitions.Def_LeanPool_PureNock_Verb
set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb

theorem Nock.Verb.map_of_mem_nodes {a : Verb} {i : Nat} {v : Verb}
    (h : (i, v) ∈ nodes a) : map i a = some v := by sorry
