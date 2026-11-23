-- Prove2me | Theorems.Thm_OBdd_discover_spec_inv
-- name    : OBdd.discover_spec_inv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:01:58.061251+00:00
-- url     : https://prove2.me/theorems/e6c591a5-5465-42d7-b4b3-36aa95b011a5
-- title:
--   OBdd: discover spec inv
-- statement:
--   `discover` is correct (backward direction): membership implies var = i and reachability.
--
--   Source: https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Reduce/Discover.lean#L70-L77
-- source:
--   https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Reduce/Discover.lean#L70-L77

import Definitions.Def_Bdd_Collect
import Definitions.Def_Bdd_Reduce_Discover
set_option autoImplicit true
open Pointer
open Bdd

theorem OBdd.discover_spec_inv {O : OBdd n m} {j : Fin m} {i : Fin n} :
    j ∈ (OBdd.discover O)[i] →
    O.1.heap[j].var.1 = i.1 ∧ Reachable O.1.heap O.1.root (.node j) := by sorry
