-- Prove2me | Theorems.Thm_OBdd_card_relevantPointer_eq_one_of_isTerminal
-- name    : OBdd.card_relevantPointer_eq_one_of_isTerminal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:04:50.614846+00:00
-- url     : https://prove2.me/theorems/9500b6a4-aca7-4162-bda2-4f667d743d82
-- title:
--   OBdd: card relevant Pointer eq one of is Terminal
-- statement:
--   The OBdd construction uses the card relevant Pointer eq one of is Terminal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Basic.lean#L1051-L1059
-- source:
--   https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Basic.lean#L1051-L1059

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

theorem OBdd.card_relevantPointer_eq_one_of_isTerminal {O : OBdd n m} : O.isTerminal → Fintype.card O.1.RelevantPointer = 1 := by sorry
