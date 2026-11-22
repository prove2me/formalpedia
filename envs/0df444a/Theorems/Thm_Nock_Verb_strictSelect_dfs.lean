-- Prove2me | Theorems.Thm_Nock_Verb_strictSelect_dfs
-- name    : Nock.Verb.strictSelect_dfs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:10:08.247188+00:00
-- url     : https://prove2.me/theorems/3da89b60-7cc1-44ca-8e02-a6e037dc4128
-- title:
--   Verb: strict Select dfs
-- statement:
--   The DFS index order is a strict total order.  This is *why* `map = DFS` "enforces a
--       strict ordering on subtrees" (main.tex:1107): distinct internal nodes get distinct `Nat`
--       indices (`enum_index_range`/`map_of_mem_nodes`), and `Nat.lt` is a strict total order.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Verb.lean#L608-L611
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Verb.lean#L608-L611

module
public import Definitions.Def_LeanPool_PureNock_Tree
public import Definitions.Def_LeanPool_PureNock_Reference
public import Definitions.Def_LeanPool_PureNock_Verb
set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb

theorem Nock.Verb.strictSelect_dfs : StrictSelect dfsLt := by sorry
