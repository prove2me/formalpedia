-- Prove2me | Theorems.Thm_Nock_BTree_dyckWordsOfLen_card
-- name    : Nock.BTree.dyckWordsOfLen_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:27:33.159795+00:00
-- url     : https://prove2.me/theorems/cb1dd920-bed0-4666-a79f-3bedaee86a2c
-- title:
--   BTree: dyck Words Of Len card
-- statement:
--   **`Lem:optimal_dyck`** (`main.tex:340–342`).
--       `|L^{2λ}_dk| = C_λ`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Dyck.lean#L348-L349
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Dyck.lean#L348-L349

module
public import Definitions.Def_LeanPool_PureNock_Tree
public import Mathlib.Combinatorics.Enumerative.Catalan.Tree
public import Definitions.Def_LeanPool_PureNock_Dyck
set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.BTree

theorem Nock.BTree.dyckWordsOfLen_card (lam : ℕ) : (dyckWordsOfLen lam).card = catalan lam := by sorry
