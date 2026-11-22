-- Prove2me | Theorems.Thm_Nock_Noun_pbt_size
-- name    : Nock.Noun.pbt_size
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:59:12.062283+00:00
-- url     : https://prove2.me/theorems/542ea929-3890-4283-9099-fa1f8d4a2312
-- title:
--   Noun: pbt size
-- statement:
--   **`Lem:pbt_size`** (`main.tex:333–335`).
--       A tree `t ∈ L_full_BT^{2λ−1}` has `λ−1` internal and `λ` leaf nodes.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Tree.lean#L68-L77
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Tree.lean#L68-L77

module
public import Definitions.Def_LeanPool_PureNock_Tree
set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Noun

theorem Nock.Noun.pbt_size (n : Noun) :
    n.size = 2 * n.leaves - 1 ∧ n.internal = n.leaves - 1 := by sorry
