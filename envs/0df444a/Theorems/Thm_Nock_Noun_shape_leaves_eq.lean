-- Prove2me | Theorems.Thm_Nock_Noun_shape_leaves_eq
-- name    : Nock.Noun.shape_leaves_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:17:30.198193+00:00
-- url     : https://prove2.me/theorems/3eccc8b9-13b9-43b9-8665-1ea980e1670d
-- title:
--   Noun: shape leaves eq
-- statement:
--   Equal shape ⇒ equal leaf count: the Dyck shape already determines `λ` (`Lem:pbt_size`,
--       main.tex:333), so it constrains how the leaf array splits between the two subtrees.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Dyck.lean#L233-L239
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Dyck.lean#L233-L239

module
public import Definitions.Def_LeanPool_PureNock_Tree
public import Mathlib.Combinatorics.Enumerative.Catalan.Tree
public import Definitions.Def_LeanPool_PureNock_Dyck
set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Noun

theorem Nock.Noun.shape_leaves_eq {n₁ n₂ : Noun} (h : n₁.shape = n₂.shape) :
    n₁.leaves = n₂.leaves := by sorry
