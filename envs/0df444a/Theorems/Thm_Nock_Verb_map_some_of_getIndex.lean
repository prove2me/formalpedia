-- Prove2me | Theorems.Thm_Nock_Verb_map_some_of_getIndex
-- name    : Nock.Verb.map_some_of_getIndex
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:04:14.231231+00:00
-- url     : https://prove2.me/theorems/3ac7f312-be41-42c1-b885-d88b134b0761
-- title:
--   Verb: map some of get Index
-- statement:
--   `getIndex a = some i` names an actual internal node: `map i a` succeeds.  (The argmax is
--       achieved at a pending node, which `map` retrieves by DFS distinctness.)
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Verb.lean#L924-L927
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Verb.lean#L924-L927

module
public import Definitions.Def_LeanPool_PureNock_Tree
public import Definitions.Def_LeanPool_PureNock_Reference
public import Definitions.Def_LeanPool_PureNock_Verb
set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb

theorem Nock.Verb.map_some_of_getIndex {a : Verb} {i : Nat} (h : getIndex a = some i) :
    ∃ sub, map i a = some sub := by sorry
