-- Prove2me | Theorems.Thm_OBdd_Canonicity_reverse
-- name    : OBdd.Canonicity_reverse
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:00:18.711827+00:00
-- url     : https://prove2.me/theorems/b231b66d-608f-4f93-9af9-af0243f848a3
-- title:
--   OBdd: Canonicity reverse
-- statement:
--   The OBdd construction uses the Canonicity reverse property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Basic.lean#L944-L946
-- source:
--   https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Basic.lean#L944-L946

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

theorem OBdd.Canonicity_reverse {O : OBdd n m} {U : OBdd n m'}:
    O.HSimilar U → O.evaluate = U.evaluate := by sorry
