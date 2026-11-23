-- Prove2me | Theorems.Thm_OBdd_usesVar_iff_dependsOn_of_reduced
-- name    : OBdd.usesVar_iff_dependsOn_of_reduced
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:00:39.251095+00:00
-- url     : https://prove2.me/theorems/aa416bf2-c1e1-432f-8c04-40d773bc03c9
-- title:
--   OBdd: uses Var iff depends On of reduced
-- statement:
--   The OBdd construction uses the uses Var iff depends On of reduced property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Basic.lean#L1608-L1619
-- source:
--   https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Basic.lean#L1608-L1619

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

theorem OBdd.usesVar_iff_dependsOn_of_reduced {O : OBdd n m} :
    O.Reduced → (O.1.usesVar i ↔ Nary.DependsOn O.evaluate i) := by sorry
