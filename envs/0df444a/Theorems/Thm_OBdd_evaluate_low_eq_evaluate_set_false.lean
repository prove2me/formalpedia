-- Prove2me | Theorems.Thm_OBdd_evaluate_low_eq_evaluate_set_false
-- name    : OBdd.evaluate_low_eq_evaluate_set_false
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T06:57:29.773942+00:00
-- url     : https://prove2.me/theorems/3aef6526-6b06-491e-a6b7-d16afafd4be1
-- title:
--   OBdd: evaluate low eq evaluate set false
-- statement:
--   The OBdd construction uses the evaluate low eq evaluate set false property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Basic.lean#L772-L784
-- source:
--   https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Basic.lean#L772-L784

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

theorem OBdd.evaluate_low_eq_evaluate_set_false {n m} {O : OBdd n m} {j : Fin m} {h : O.1.root = node j} :
    (O.low h).evaluate = O.evaluate ∘ fun I ↦ I.set O.1.heap[j].var false := by sorry
