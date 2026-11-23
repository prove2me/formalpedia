-- Prove2me | Theorems.Thm_OBdd_low_oreachable
-- name    : OBdd.low_oreachable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:04:51.190849+00:00
-- url     : https://prove2.me/theorems/98a49039-ee9a-4a69-b85c-06c402ca4992
-- title:
--   OBdd: low oreachable
-- statement:
--   The OBdd construction uses the low oreachable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Basic.lean#L1024-L1025
-- source:
--   https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Basic.lean#L1024-L1025

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

theorem OBdd.low_oreachable {n m} {j} {O U : OBdd n m} {U_root_def : U.1.root = node j}: O.OReachable U → O.OReachable (U.low U_root_def) := by sorry
