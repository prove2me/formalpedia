-- Prove2me | Theorems.Thm_OBdd_discover_spec
-- name    : OBdd.discover_spec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:01:57.972817+00:00
-- url     : https://prove2.me/theorems/c15f1181-3eb2-4dfc-8eed-8f87d87ad076
-- title:
--   OBdd: discover spec
-- statement:
--   `discover` is correct (forward direction).
--
--   Source: https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Reduce/Discover.lean#L42-L44
-- source:
--   https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Reduce/Discover.lean#L42-L44

import Definitions.Def_Bdd_Collect
import Definitions.Def_Bdd_Reduce_Discover
set_option autoImplicit true
open Pointer
open Bdd

theorem OBdd.discover_spec {O : OBdd n m} {j : Fin m} :
    (Reachable O.1.heap O.1.root (node j)) → j ∈ (OBdd.discover O)[O.1.heap[j].var] := by sorry
