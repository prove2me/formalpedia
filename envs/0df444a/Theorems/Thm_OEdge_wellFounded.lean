-- Prove2me | Theorems.Thm_OEdge_wellFounded
-- name    : OEdge.wellFounded
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:02:22.379234+00:00
-- url     : https://prove2.me/theorems/1d38ea20-4de8-4382-83bb-1a5e786dcb48
-- title:
--   OEdge: well Founded
-- statement:
--   The `OEdge` relation between Ordered BDDs is well-founded.
--
--   Source: https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Basic.lean#L190-L203
-- source:
--   https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Basic.lean#L190-L203

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

theorem OEdge.wellFounded {n m} : @WellFounded (OBdd n m) OEdge := by sorry
