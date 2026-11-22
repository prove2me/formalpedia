-- Prove2me | Theorems.Thm_Nock_BTree_exists_encode_of_dyck
-- name    : Nock.BTree.exists_encode_of_dyck
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:09:17.976127+00:00
-- url     : https://prove2.me/theorems/30f58c9b-c2f0-4d69-92d3-f04ad2d20e57
-- title:
--   BTree: exists encode of dyck
-- statement:
--   Every Dyck word is the encoding of some tree (surjectivity of `encode` onto `L_dk`).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Dyck.lean#L77-L83
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Dyck.lean#L77-L83

module
public import Definitions.Def_LeanPool_PureNock_Tree
public import Mathlib.Combinatorics.Enumerative.Catalan.Tree
public import Definitions.Def_LeanPool_PureNock_Dyck
set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.BTree

theorem Nock.BTree.exists_encode_of_dyck {w : List Bool} (h : Dyck w) : ∃ t : BTree, encode t = w := by sorry
