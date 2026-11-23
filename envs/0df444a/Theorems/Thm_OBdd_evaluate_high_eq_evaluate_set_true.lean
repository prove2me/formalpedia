-- Prove2me | Theorems.Thm_OBdd_evaluate_high_eq_evaluate_set_true
-- name    : OBdd.evaluate_high_eq_evaluate_set_true
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T06:57:22.835848+00:00
-- url     : https://prove2.me/theorems/06a35876-3b7c-4f91-8e67-6a5d014a3acc
-- title:
--   OBdd: evaluate high eq evaluate set true
-- statement:
--   The OBdd construction uses the evaluate high eq evaluate set true property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Basic.lean#L759-L770
-- source:
--   https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Basic.lean#L759-L770

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

theorem OBdd.evaluate_high_eq_evaluate_set_true {n m} {O : OBdd n m} {j : Fin m} {h : O.1.root = node j} :
    (O.high h).evaluate = O.evaluate ∘ fun I ↦ I.set O.1.heap[j].var true := by sorry
