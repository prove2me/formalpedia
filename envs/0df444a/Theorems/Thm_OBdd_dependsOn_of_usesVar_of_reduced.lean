-- Prove2me | Theorems.Thm_OBdd_dependsOn_of_usesVar_of_reduced
-- name    : OBdd.dependsOn_of_usesVar_of_reduced
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:00:37.804428+00:00
-- url     : https://prove2.me/theorems/9174259d-3ae1-487d-8de6-68e2d183380d
-- title:
--   OBdd: depends On of uses Var of reduced
-- statement:
--   The OBdd construction uses the depends On of uses Var of reduced property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Basic.lean#L1456-L1564
-- source:
--   https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Basic.lean#L1456-L1564

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

theorem OBdd.dependsOn_of_usesVar_of_reduced {O : OBdd n m} :
    O.Reduced → Reachable O.1.heap O.1.root (node j) → O.1.heap[j].var = i → ∃ v : Vector Bool n, O.evaluate v ≠ O.evaluate (v.set i true) := by sorry
