-- Prove2me | Theorems.Thm_Nock_Noun_shape_size
-- name    : Nock.Noun.shape_size
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:09:22.490108+00:00
-- url     : https://prove2.me/theorems/c4ea7d8a-0763-4534-aa67-ac599a9280ee
-- title:
--   Noun: shape size
-- statement:
--   The shape preserves leaf and node counts (`Noun.size = BTree.size ∘ shape`).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Dyck.lean#L196-L199
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Dyck.lean#L196-L199

module
public import Definitions.Def_LeanPool_PureNock_Tree
public import Mathlib.Combinatorics.Enumerative.Catalan.Tree
public import Definitions.Def_LeanPool_PureNock_Dyck
set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Noun

theorem Nock.Noun.shape_size (n : Noun) : n.shape.size = n.size := by sorry
