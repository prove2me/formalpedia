-- Prove2me | Theorems.Thm_OBdd_eq_root_disjoint_reachable_low_or_high
-- name    : OBdd.eq_root_disjoint_reachable_low_or_high
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:00:28.843519+00:00
-- url     : https://prove2.me/theorems/3bb71705-2e1c-49e9-a10f-03da5f0ffe91
-- title:
--   OBdd: eq root disjoint reachable low or high
-- statement:
--   The OBdd construction uses the eq root disjoint reachable low or high property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Basic.lean#L1192-L1206
-- source:
--   https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Basic.lean#L1192-L1206

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

theorem OBdd.eq_root_disjoint_reachable_low_or_high {O : OBdd n m} (h : O.1.root = node j) :
    Disjoint
      (· = O.1.root)
      (fun p ↦ (Reachable O.1.heap (O.low  h).1.root p ∨ Reachable O.1.heap (O.high h).1.root p)) := by sorry
