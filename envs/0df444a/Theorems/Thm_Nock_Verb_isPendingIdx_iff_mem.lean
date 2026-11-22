-- Prove2me | Theorems.Thm_Nock_Verb_isPendingIdx_iff_mem
-- name    : Nock.Verb.isPendingIdx_iff_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:06:25.890907+00:00
-- url     : https://prove2.me/theorems/4d30d712-3e05-4fd4-aad5-3c2ddaa1eb56
-- title:
--   Verb: is Pending Idx iff mem
-- statement:
--   Pending-index membership, in list form.  The `←` direction uses DFS distinctness
--       (`map_of_mem_nodes`): a pending node in the `nodes` list is retrieved by `map` on its
--       (unique) index.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Verb.lean#L616-L620
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Verb.lean#L616-L620

module
public import Definitions.Def_LeanPool_PureNock_Tree
public import Definitions.Def_LeanPool_PureNock_Reference
public import Definitions.Def_LeanPool_PureNock_Verb
set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb

theorem Nock.Verb.isPendingIdx_iff_mem {a : Verb} {i : Nat} :
    IsPendingIdx a i ↔ ∃ v, (i, v) ∈ nodes a ∧ v.isPending = true := by sorry
