-- Prove2me | Theorems.Thm_Front_tree_shrink_subset
-- name    : Front.tree_shrink_subset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:43:47.243388+00:00
-- url     : https://prove2.me/theorems/106d19e4-5aa6-48f5-87c1-7baf3ff0af55
-- title:
--   Front: tree shrink subset
-- statement:
--   The tree of a restriction is contained in the tree of the front.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NashWilliams/Combinatorics/Front/Shrink.lean#L129-L131
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NashWilliams/Combinatorics/Front/Shrink.lean#L129-L131

module
public import Definitions.Def_LeanPool_NashWilliams_Combinatorics_Front_Rank
public import Definitions.Def_LeanPool_NashWilliams_Combinatorics_Front_Shrink
set_option autoImplicit true
@[expose] public section
public section
open Set List
noncomputable section
open Front
variable {F : Set (List ℕ)} {M : ℕ → ℕ}

theorem Front.tree_shrink_subset {N : ℕ → ℕ} : tree (shrink F N) ⊆ tree F := by sorry
