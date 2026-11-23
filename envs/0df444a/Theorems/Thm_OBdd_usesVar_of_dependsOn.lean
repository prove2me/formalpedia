-- Prove2me | Theorems.Thm_OBdd_usesVar_of_dependsOn
-- name    : OBdd.usesVar_of_dependsOn
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T06:59:15.710659+00:00
-- url     : https://prove2.me/theorems/73ea8d28-4d28-4bf6-a686-4d6f0e8923de
-- title:
--   OBdd: uses Var of depends On
-- statement:
--   The OBdd construction uses the uses Var of depends On property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Basic.lean#L1566-L1606
-- source:
--   https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Basic.lean#L1566-L1606

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

theorem OBdd.usesVar_of_dependsOn {O : OBdd n m} {i : Fin n} :
    O.evaluate v ≠ O.evaluate (v.set i b) → O.1.usesVar i := by sorry
