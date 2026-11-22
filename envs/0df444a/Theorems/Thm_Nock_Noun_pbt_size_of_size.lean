-- Prove2me | Theorems.Thm_Nock_Noun_pbt_size_of_size
-- name    : Nock.Noun.pbt_size_of_size
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:59:11.654937+00:00
-- url     : https://prove2.me/theorems/7540e227-486e-4919-855f-0412ea418484
-- title:
--   Noun: pbt size of size
-- statement:
--   **`Lem:pbt_size`** (`main.tex:333–335`).
--       A tree `t ∈ L_full_BT^{2λ−1}` has `λ−1` internal and `λ` leaf nodes.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Tree.lean#L82-L86
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Tree.lean#L82-L86

module
public import Definitions.Def_LeanPool_PureNock_Tree
set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Noun

theorem Nock.Noun.pbt_size_of_size {n : Noun} {lam : Nat} (hlam : 1 ≤ lam)
    (h : n.size = 2 * lam - 1) : n.leaves = lam ∧ n.internal = lam - 1 := by sorry
