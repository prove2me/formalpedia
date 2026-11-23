-- Prove2me | Theorems.Thm_OBdd_card_RelevantPointer_le
-- name    : OBdd.card_RelevantPointer_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:04:53.219174+00:00
-- url     : https://prove2.me/theorems/81e80898-5271-420d-9942-1a60bbcdf66e
-- title:
--   OBdd: card Relevant Pointer le
-- statement:
--   The OBdd construction uses the card Relevant Pointer le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Basic.lean#L1030-L1049
-- source:
--   https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Basic.lean#L1030-L1049

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

theorem OBdd.card_RelevantPointer_le {O : OBdd n m} : Fintype.card O.1.RelevantPointer ≤ m + 2 := by sorry
