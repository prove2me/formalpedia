-- Prove2me | Theorems.Thm_Nock_BTree_dyck_iff_encode
-- name    : Nock.BTree.dyck_iff_encode
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:17:22.182806+00:00
-- url     : https://prove2.me/theorems/a481c0cc-6551-4523-98a8-8fc739577997
-- title:
--   BTree: dyck iff encode
-- statement:
--   **`Lem:optimal_dyck`** (`main.tex:340–342`).
--       `L_dk ≡ L_full_BT`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Dyck.lean#L169-L170
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Dyck.lean#L169-L170

module
public import Definitions.Def_LeanPool_PureNock_Tree
public import Mathlib.Combinatorics.Enumerative.Catalan.Tree
public import Definitions.Def_LeanPool_PureNock_Dyck
set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.BTree

theorem Nock.BTree.dyck_iff_encode {w : List Bool} : Dyck w ↔ ∃ t : BTree, encode t = w := by sorry
