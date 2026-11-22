-- Prove2me | Theorems.Thm_Nock_BTree_mem_dyckWordsOfLen
-- name    : Nock.BTree.mem_dyckWordsOfLen
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:27:23.843361+00:00
-- url     : https://prove2.me/theorems/da5e16b2-6ddc-40c1-8ddd-b8be1f9e930c
-- title:
--   BTree: mem dyck Words Of Len
-- statement:
--   A word lies in `dyckWordsOfLen λ` iff it is a Dyck word of length `2λ` — i.e. this finset is
--       exactly the paper's `L^{2λ}_dk`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Dyck.lean#L325-L343
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Dyck.lean#L325-L343

module
public import Definitions.Def_LeanPool_PureNock_Tree
public import Mathlib.Combinatorics.Enumerative.Catalan.Tree
public import Definitions.Def_LeanPool_PureNock_Dyck
set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.BTree

theorem Nock.BTree.mem_dyckWordsOfLen {lam : ℕ} {w : List Bool} :
    w ∈ dyckWordsOfLen lam ↔ Dyck w ∧ w.length = 2 * lam := by sorry
