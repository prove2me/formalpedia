-- Prove2me | Theorems.Thm_OBdd_var_lt_high_var
-- name    : OBdd.var_lt_high_var
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T06:55:11.801802+00:00
-- url     : https://prove2.me/theorems/aae59f4f-aa6f-43c6-ae51-58f73c5b083e
-- title:
--   OBdd: var lt high var
-- statement:
--   The OBdd construction uses the var lt high var property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Basic.lean#L690-L693
-- source:
--   https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Basic.lean#L690-L693

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

theorem OBdd.var_lt_high_var {O : OBdd n m} {h : O.1.root = node j} :
    O.var < (O.high h).var := by sorry
