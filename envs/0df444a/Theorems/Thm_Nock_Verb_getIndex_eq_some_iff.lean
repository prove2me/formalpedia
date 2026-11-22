-- Prove2me | Theorems.Thm_Nock_Verb_getIndex_eq_some_iff
-- name    : Nock.Verb.getIndex_eq_some_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:00:31.786686+00:00
-- url     : https://prove2.me/theorems/4b3482b2-b434-4e9c-8690-410239f2a644
-- title:
--   Verb: get Index eq some iff
-- statement:
--   `getIndex` is exactly the DFS argmax: `getIndex a = some i ↔ i` is the maximal pending
--       index under `dfsLt`.  (Combines the `maximumPendingIndex` spec with DFS distinctness.)
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Verb.lean#L624-L642
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Verb.lean#L624-L642

module
public import Definitions.Def_LeanPool_PureNock_Tree
public import Definitions.Def_LeanPool_PureNock_Reference
public import Definitions.Def_LeanPool_PureNock_Verb
set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb

theorem Nock.Verb.getIndex_eq_some_iff {a : Verb} {i : Nat} :
    getIndex a = some i ↔ IsMaxPending dfsLt a i := by sorry
