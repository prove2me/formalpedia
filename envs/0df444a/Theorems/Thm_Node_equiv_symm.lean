-- Prove2me | Theorems.Thm_Node_equiv_symm
-- name    : Node.equiv_symm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T06:58:12.015251+00:00
-- url     : https://prove2.me/theorems/e56a0718-ec05-4ef0-b64c-a1fcee3c7d5c
-- title:
--   Node: equiv symm
-- statement:
--   The Node construction uses the equiv symm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Basic.lean#L1897-L1903
-- source:
--   https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Basic.lean#L1897-L1903

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

theorem Node.equiv_symm : Node.equiv N M → Node.equiv M N := by sorry
