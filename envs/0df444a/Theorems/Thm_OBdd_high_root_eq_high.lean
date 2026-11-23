-- Prove2me | Theorems.Thm_OBdd_high_root_eq_high
-- name    : OBdd.high_root_eq_high
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T06:58:02.151803+00:00
-- url     : https://prove2.me/theorems/20d4c614-298a-4f06-a514-8ff02f88c6a0
-- title:
--   OBdd: high root eq high
-- statement:
--   The OBdd construction uses the high root eq high property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Basic.lean#L305-L305
-- source:
--   https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Basic.lean#L305-L305

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

theorem OBdd.high_root_eq_high {O : OBdd n m} {h : O.1.root = node j} : (O.high h).1.root = O.1.heap[j].high := by sorry
