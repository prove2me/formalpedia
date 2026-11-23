-- Prove2me | Theorems.Thm_OBdd_not_oedge_reachable
-- name    : OBdd.not_oedge_reachable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T06:57:48.411422+00:00
-- url     : https://prove2.me/theorems/a9708fc7-b15c-4569-a6a9-d03012d884fc
-- title:
--   OBdd: not oedge reachable
-- statement:
--   An acyclicity lemma: an edge from `O` to `U` implies that `O` is not reachable from `U`.
--
--   Source: https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Basic.lean#L949-L970
-- source:
--   https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Basic.lean#L949-L970

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

theorem OBdd.not_oedge_reachable {n m} {O U : OBdd n m}: OEdge O U → ¬ Reachable O.1.heap U.1.root O.1.root := by sorry
