-- Prove2me | Theorems.Thm_OBdd_reachable_or_eq_low_high
-- name    : OBdd.reachable_or_eq_low_high
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T06:59:12.870554+00:00
-- url     : https://prove2.me/theorems/58d6cd69-5589-4070-8108-9c1ab2980d34
-- title:
--   OBdd: reachable or eq low high
-- statement:
--   The OBdd construction uses the reachable or eq low high property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Basic.lean#L1004-L1015
-- source:
--   https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Basic.lean#L1004-L1015

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

theorem OBdd.reachable_or_eq_low_high {O : OBdd n m} :
    Reachable O.1.heap O.1.root p → (O.1.root = p ∨ (∃ j, ∃ (h : O.1.root = node j), (Reachable O.1.heap (O.low h).1.root p ∨ Reachable O.1.heap (O.high h).1.root p))) := by sorry
