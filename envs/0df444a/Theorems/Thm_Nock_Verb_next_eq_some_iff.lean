-- Prove2me | Theorems.Thm_Nock_Verb_next_eq_some_iff
-- name    : Nock.Verb.next_eq_some_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:00:34.377165+00:00
-- url     : https://prove2.me/theorems/68cc2a89-1746-449e-be58-eb2830f2619e
-- title:
--   Verb: next eq some iff
-- statement:
--   **`next` faithfully realizes the strict DFS selection step.**  This is the bridge that
--       makes `deterministic_Trace` an instance of the paper's conditional theorem: the concrete
--       interpreter's step is `SelStep` for the (strict) DFS order.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Verb.lean#L648-L670
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Verb.lean#L648-L670

module
public import Definitions.Def_LeanPool_PureNock_Tree
public import Definitions.Def_LeanPool_PureNock_Reference
public import Definitions.Def_LeanPool_PureNock_Verb
set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb

theorem Nock.Verb.next_eq_some_iff {a b : Verb} : next a = some b ↔ SelStep dfsLt a b := by sorry
