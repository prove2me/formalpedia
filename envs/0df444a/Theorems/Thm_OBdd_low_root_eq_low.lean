-- Prove2me | Theorems.Thm_OBdd_low_root_eq_low
-- name    : OBdd.low_root_eq_low
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T06:57:58.072801+00:00
-- url     : https://prove2.me/theorems/bf1d6103-b02c-4649-bcd3-862734607e14
-- title:
--   OBdd: low root eq low
-- statement:
--   The OBdd construction uses the low root eq low property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Basic.lean#L301-L301
-- source:
--   https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Basic.lean#L301-L301

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

theorem OBdd.low_root_eq_low {O : OBdd n m} {h : O.1.root = node j} : (O.low h).1.root = O.1.heap[j].low := by sorry
