-- Prove2me | Theorems.Thm_OBdd_not_reduced_of_sim_high_low
-- name    : OBdd.not_reduced_of_sim_high_low
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T06:57:44.904519+00:00
-- url     : https://prove2.me/theorems/473d8c1d-83c8-479b-ac2d-8fbe02709cd4
-- title:
--   OBdd: not reduced of sim high low
-- statement:
--   The OBdd construction uses the not reduced of sim high low property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Basic.lean#L800-L809
-- source:
--   https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Basic.lean#L800-L809

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

theorem OBdd.not_reduced_of_sim_high_low {n m} {O : OBdd n m} {j : Fin m} (h : O.1.root = node j) :
    Similar (O.high h) (O.low h) → ¬ O.Reduced := by sorry
