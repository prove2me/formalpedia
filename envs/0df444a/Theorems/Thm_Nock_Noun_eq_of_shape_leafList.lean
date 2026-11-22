-- Prove2me | Theorems.Thm_Nock_Noun_eq_of_shape_leafList
-- name    : Nock.Noun.eq_of_shape_leafList
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:17:31.125432+00:00
-- url     : https://prove2.me/theorems/a4c837ad-b32e-496d-96e4-41d7cd278fbf
-- title:
--   Noun: eq of shape leaf List
-- statement:
--   **Reconstruction.**  If two nouns have the same shape (Dyck word) and the same leaf
--       array, they are the *same* noun: the shape fixes the tree structure and the leaf list
--       fills the leaves in DFS order, leaving no ambiguity.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Dyck.lean#L245-L266
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Dyck.lean#L245-L266

module
public import Definitions.Def_LeanPool_PureNock_Tree
public import Mathlib.Combinatorics.Enumerative.Catalan.Tree
public import Definitions.Def_LeanPool_PureNock_Dyck
set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Noun

theorem Nock.Noun.eq_of_shape_leafList :
    ∀ {n₁ n₂ : Noun}, n₁.shape = n₂.shape → n₁.leafList = n₂.leafList → n₁ = n₂ := by sorry
