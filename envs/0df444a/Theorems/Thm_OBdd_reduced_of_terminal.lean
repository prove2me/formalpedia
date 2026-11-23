-- Prove2me | Theorems.Thm_OBdd_reduced_of_terminal
-- name    : OBdd.reduced_of_terminal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T06:55:14.858265+00:00
-- url     : https://prove2.me/theorems/b824a67e-d6f3-44cb-afe9-30995cd20f7e
-- title:
--   OBdd: reduced of terminal
-- statement:
--   Terminal BDDs are reduced.
--
--   Source: https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Basic.lean#L574-L583
-- source:
--   https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Basic.lean#L574-L583

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

theorem OBdd.reduced_of_terminal {n m} {O : OBdd n m} : O.isTerminal → O.Reduced := by sorry
