-- Prove2me | Theorems.Thm_OBdd_evaluate_eq_evaluate_of_ordered_heap_all_reachable_eq
-- name    : OBdd.evaluate_eq_evaluate_of_ordered_heap_all_reachable_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T06:58:16.435436+00:00
-- url     : https://prove2.me/theorems/cd86a4dc-2f5e-4eeb-a4a6-7b9defc600bd
-- title:
--   OBdd: evaluate eq evaluate of ordered heap all reachable eq
-- statement:
--   The OBdd construction uses the evaluate eq evaluate of ordered heap all reachable eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Basic.lean#L2039-L2046
-- source:
--   https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Basic.lean#L2039-L2046

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

theorem OBdd.evaluate_eq_evaluate_of_ordered_heap_all_reachable_eq (O : OBdd n m) (U : OBdd n m') :
    (∀ j : Fin m', Reachable U.1.heap U.1.root (node j) → ∃ hj : j.1 < m, Node.equiv O.1.heap[j.1] U.1.heap[j]) →
    Pointer.equiv U.1.root O.1.root →
    O.evaluate = U.evaluate := by sorry
