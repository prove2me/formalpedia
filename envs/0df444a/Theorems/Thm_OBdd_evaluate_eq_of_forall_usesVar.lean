-- Prove2me | Theorems.Thm_OBdd_evaluate_eq_of_forall_usesVar
-- name    : OBdd.evaluate_eq_of_forall_usesVar
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:05:29.504181+00:00
-- url     : https://prove2.me/theorems/b49f7628-977e-4cfc-8c85-9e5177de728b
-- title:
--   OBdd: evaluate eq of forall uses Var
-- statement:
--   The OBdd construction uses the evaluate eq of forall uses Var property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Basic.lean#L1715-L1723
-- source:
--   https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Basic.lean#L1715-L1723

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

theorem OBdd.evaluate_eq_of_forall_usesVar {O : OBdd n m} {I J : Vector Bool n} :
    (∀ i, O.1.usesVar i → I[i] = J[i]) → O.evaluate I = O.evaluate J := by sorry
