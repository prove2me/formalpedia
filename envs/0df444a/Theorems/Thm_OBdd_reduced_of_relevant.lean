-- Prove2me | Theorems.Thm_OBdd_reduced_of_relevant
-- name    : OBdd.reduced_of_relevant
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T06:59:00.965779+00:00
-- url     : https://prove2.me/theorems/d921a3fb-af89-4b2c-bd27-50d5c34c4bee
-- title:
--   OBdd: reduced of relevant
-- statement:
--   Sub-BDDs of a reduced BDD are reduced.
--
--   Source: https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Basic.lean#L588-L605
-- source:
--   https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Basic.lean#L588-L605

import Mathlib.Data.Fintype.Sum
import Init.Data.ToString.Basic
import Mathlib.Tactic.DeriveFintype
import Mathlib.Data.Fintype.Vector
import Mathlib.Tactic.Linarith
import Definitions.Def_Bdd_Nary
import Definitions.Def_Bdd_DecisionTree
import Definitions.Def_Bdd_Basic
set_option autoImplicit true
open Pointer
open Bdd
attribute [local instance_reducible] OBdd Bdd.Ordered

theorem OBdd.reduced_of_relevant {O : OBdd n m} (S : O.1.RelevantPointer):
    O.Reduced → OBdd.Reduced ⟨{heap := O.1.heap, root := S.1}, ordered_of_relevant O S⟩ := by sorry
