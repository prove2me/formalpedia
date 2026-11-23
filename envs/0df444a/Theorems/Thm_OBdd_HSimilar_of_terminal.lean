-- Prove2me | Theorems.Thm_OBdd_HSimilar_of_terminal
-- name    : OBdd.HSimilar_of_terminal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:03:00.23858+00:00
-- url     : https://prove2.me/theorems/922d6388-4924-4b2f-b764-0b89c3bb1094
-- title:
--   OBdd: HSimilar of terminal
-- statement:
--   The OBdd construction uses the HSimilar of terminal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Basic.lean#L668-L672
-- source:
--   https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Basic.lean#L668-L672

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

theorem OBdd.HSimilar_of_terminal {n m m' : Nat} {b : Bool} {O : OBdd n m} {U : OBdd n m'} :
    O.1.root = terminal b → U.1.root = terminal b → O.HSimilar U := by sorry
