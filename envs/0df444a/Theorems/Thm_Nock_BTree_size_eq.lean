-- Prove2me | Theorems.Thm_Nock_BTree_size_eq
-- name    : Nock.BTree.size_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:17:35.498658+00:00
-- url     : https://prove2.me/theorems/4da8ab51-5901-4e38-87b0-49a6dc2f3d7a
-- title:
--   BTree: size eq
-- statement:
--   Under the shape isomorphism, `BTree.size` is `2·numNodes + 1`: a proper binary tree with
--       `λ` internal (Mathlib) nodes has `2λ+1` total nodes (`Lem:pbt_size`, main.tex:333).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Dyck.lean#L306-L311
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Dyck.lean#L306-L311

module
public import Definitions.Def_LeanPool_PureNock_Tree
public import Mathlib.Combinatorics.Enumerative.Catalan.Tree
public import Definitions.Def_LeanPool_PureNock_Dyck
set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.BTree

theorem Nock.BTree.size_eq (t : BTree) : t.size = 2 * (toBin t).numNodes + 1 := by sorry
