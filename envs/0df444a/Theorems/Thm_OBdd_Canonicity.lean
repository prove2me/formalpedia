-- Prove2me | Theorems.Thm_OBdd_Canonicity
-- name    : OBdd.Canonicity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T06:57:43.738631+00:00
-- url     : https://prove2.me/theorems/9b364cdf-407e-4971-aa8b-9b6488df92e8
-- title:
--   OBdd: Canonicity
-- statement:
--   Reduced OBDDs are canonical.
--
--   Source: https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Basic.lean#L834-L921
-- source:
--   https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Basic.lean#L834-L921

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

theorem OBdd.Canonicity {O : OBdd n m} {U : OBdd n m'} (ho : O.Reduced) (hu : U.Reduced) :
    O.evaluate = U.evaluate → O.HSimilar U := by sorry
