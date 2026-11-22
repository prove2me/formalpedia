-- Prove2me | Theorems.Thm_Nock_BTree_dyck_length_graded
-- name    : Nock.BTree.dyck_length_graded
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:26:26.731086+00:00
-- url     : https://prove2.me/theorems/d9f648a9-dfe0-4ac5-a31e-e366c019afbd
-- title:
--   BTree: dyck length graded
-- statement:
--   **`Lem:optimal_dyck`** (`main.tex:340–342`).
--       `∀λ, L^{2λ}_dk ≡ L^{2λ+1}_full_BT`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Dyck.lean#L175-L179
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Dyck.lean#L175-L179

module
public import Definitions.Def_LeanPool_PureNock_Tree
public import Mathlib.Combinatorics.Enumerative.Catalan.Tree
public import Definitions.Def_LeanPool_PureNock_Dyck
set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.BTree

theorem Nock.BTree.dyck_length_graded {w : List Bool} (t : BTree) (ht : encode t = w) (lam : Nat) :
    w.length = 2 * lam ↔ t.size = 2 * lam + 1 := by sorry
