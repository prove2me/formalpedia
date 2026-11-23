-- Prove2me | Theorems.Thm_OBdd_toTree_usesVar
-- name    : OBdd.toTree_usesVar
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:00:37.935544+00:00
-- url     : https://prove2.me/theorems/5dfaa4d7-4844-44da-a452-669531bcecee
-- title:
--   OBdd: to Tree uses Var
-- statement:
--   The OBdd construction uses the to Tree uses Var property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Basic.lean#L1667-L1713
-- source:
--   https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Basic.lean#L1667-L1713

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

theorem OBdd.toTree_usesVar {O : OBdd n m} : O.1.usesVar i ↔ O.toTree.usesVar i := by sorry
