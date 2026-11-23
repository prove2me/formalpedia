-- Prove2me | Theorems.Thm_OBdd_evaluate_low_eq_of_evaluate_eq_and_var_eq
-- name    : OBdd.evaluate_low_eq_of_evaluate_eq_and_var_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:03:37.268882+00:00
-- url     : https://prove2.me/theorems/e33e4720-5af9-4b4e-8c82-ce5c49e55f03
-- title:
--   OBdd: evaluate low eq of evaluate eq and var eq
-- statement:
--   The OBdd construction uses the evaluate low eq of evaluate eq and var eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Basic.lean#L797-L798
-- source:
--   https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Basic.lean#L797-L798

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

theorem OBdd.evaluate_low_eq_of_evaluate_eq_and_var_eq {n m} {O U : OBdd n m} {j i : Fin m} {ho : O.1.root = node j} {hu : U.1.root = node i} :
  O.evaluate = U.evaluate → O.1.heap[j].var = U.1.heap[i].var → (O.low ho).evaluate = (U.low hu).evaluate := by sorry
