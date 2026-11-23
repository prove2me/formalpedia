-- Prove2me | Theorems.Thm_OBdd_independentOf_lt_root
-- name    : OBdd.independentOf_lt_root
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T06:55:09.427345+00:00
-- url     : https://prove2.me/theorems/3bec198f-4cef-4d4c-afde-2a1132dfa1b2
-- title:
--   OBdd: independent Of lt root
-- statement:
--   The OBdd construction uses the independent Of lt root property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Basic.lean#L700-L716
-- source:
--   https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Basic.lean#L700-L716

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

theorem OBdd.independentOf_lt_root (O : OBdd n m) (i : Fin O.var) :
    Nary.IndependentOf (O.evaluate) ⟨i.1, Fin.val_lt_of_le i (Fin.is_le _)⟩ := by sorry
