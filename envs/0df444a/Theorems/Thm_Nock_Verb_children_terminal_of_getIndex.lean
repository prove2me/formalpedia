-- Prove2me | Theorems.Thm_Nock_Verb_children_terminal_of_getIndex
-- name    : Nock.Verb.children_terminal_of_getIndex
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:03:00.032076+00:00
-- url     : https://prove2.me/theorems/4ff0e2f4-4212-4ccc-8a9d-4239aede5581
-- title:
--   Verb: children terminal of get Index
-- statement:
--   **The selected redex has terminal children.**  If `getIndex v = some i` picks the argmax
--       pending node `map i v = node a l r`, then `l` and `r` are terminal: any pending node below
--       them would have a strictly larger DFS index (`enum_index_range` + `enum_subtree_mem`),
--       contradicting maximality (`getIndex_eq_some_iff`).  This is the shape `inDomain`/`reduce`
--       need at the redex.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Verb.lean#L800-L827
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Verb.lean#L800-L827

module
public import Definitions.Def_LeanPool_PureNock_Tree
public import Definitions.Def_LeanPool_PureNock_Reference
public import Definitions.Def_LeanPool_PureNock_Verb
set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb

theorem Nock.Verb.children_terminal_of_getIndex {v : Verb} {i : Nat} {a : Action} {l r : Verb}
    (hidx : getIndex v = some i) (hmap : map i v = some (Verb.node a l r)) :
    isTerminal l = true ∧ isTerminal r = true := by sorry
