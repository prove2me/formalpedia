-- Prove2me | Theorems.Thm_Nock_Noun_size_eq_leaves_add_internal
-- name    : Nock.Noun.size_eq_leaves_add_internal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:59:11.938578+00:00
-- url     : https://prove2.me/theorems/6e107574-2c34-4059-9928-e039fbc2306c
-- title:
--   Noun: size eq leaves add internal
-- statement:
--   Every node of a proper binary tree is a leaf or an internal node:
--       `size = leaves + internal`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Tree.lean#L90-L93
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Tree.lean#L90-L93

module
public import Definitions.Def_LeanPool_PureNock_Tree
set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Noun

theorem Nock.Noun.size_eq_leaves_add_internal (n : Noun) : n.size = n.leaves + n.internal := by sorry
