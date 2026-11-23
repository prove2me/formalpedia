-- Prove2me | Theorems.Thm_OBdd_terminal_of_constant
-- name    : OBdd.terminal_of_constant
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:04:23.957856+00:00
-- url     : https://prove2.me/theorems/d4b9177c-c0e1-461a-8d41-a80042bb9d5c
-- title:
--   OBdd: terminal of constant
-- statement:
--   The only reduced BDD that denotes a constant function is the terminal BDD.
--
--   Source: https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Basic.lean#L924-L942
-- source:
--   https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Basic.lean#L924-L942

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

theorem OBdd.terminal_of_constant (O : OBdd n m) :
    O.Reduced → O.evaluate = (fun _ ↦ b) → O.1.root = terminal b := by sorry
