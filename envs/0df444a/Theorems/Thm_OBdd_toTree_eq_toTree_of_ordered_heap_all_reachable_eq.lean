-- Prove2me | Theorems.Thm_OBdd_toTree_eq_toTree_of_ordered_heap_all_reachable_eq
-- name    : OBdd.toTree_eq_toTree_of_ordered_heap_all_reachable_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T06:59:19.242464+00:00
-- url     : https://prove2.me/theorems/32616507-4400-42be-8b07-0620675f4044
-- title:
--   OBdd: to Tree eq to Tree of ordered heap all reachable eq
-- statement:
--   The OBdd construction uses the to Tree eq to Tree of ordered heap all reachable eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Basic.lean#L1996-L2037
-- source:
--   https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Basic.lean#L1996-L2037

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

theorem OBdd.toTree_eq_toTree_of_ordered_heap_all_reachable_eq (O : OBdd n m) (U : OBdd n m') :
    (∀ j : Fin m', Reachable U.1.heap U.1.root (node j) → ∃ hj : j.1 < m, Node.equiv O.1.heap[j.1] U.1.heap[j]) →
    Pointer.equiv U.1.root O.1.root →
    O.toTree = U.toTree := by sorry
