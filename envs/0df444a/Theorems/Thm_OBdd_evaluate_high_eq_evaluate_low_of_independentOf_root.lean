-- Prove2me | Theorems.Thm_OBdd_evaluate_high_eq_evaluate_low_of_independentOf_root
-- name    : OBdd.evaluate_high_eq_evaluate_low_of_independentOf_root
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:00:11.367249+00:00
-- url     : https://prove2.me/theorems/ecd1f8ef-cb8b-4f12-b86e-3fcb1bd318f5
-- title:
--   OBdd: evaluate high eq evaluate low of independent Of root
-- statement:
--   The OBdd construction uses the evaluate high eq evaluate low of independent Of root property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Basic.lean#L744-L757
-- source:
--   https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Basic.lean#L744-L757

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

theorem OBdd.evaluate_high_eq_evaluate_low_of_independentOf_root {n m} {O : OBdd n m} {j : Fin m} {h : O.1.root = node j} :
    Nary.IndependentOf O.evaluate O.1.heap[j].var → (O.high h).evaluate = (O.low h).evaluate := by sorry
