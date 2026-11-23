-- Prove2me | Theorems.Thm_OBdd_size_zero_of_terminal
-- name    : OBdd.size_zero_of_terminal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:03:04.530875+00:00
-- url     : https://prove2.me/theorems/a6fc2bba-c5d1-455d-a4c9-a08fca25d906
-- title:
--   OBdd: size zero of terminal
-- statement:
--   The OBdd construction uses the size zero of terminal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Basic.lean#L720-L724
-- source:
--   https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Basic.lean#L720-L724

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

theorem OBdd.size_zero_of_terminal : OBdd.isTerminal O → O.size' = 0 := by sorry
