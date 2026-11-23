-- Prove2me | Theorems.Thm_OBdd_reduced_var_dependent
-- name    : OBdd.reduced_var_dependent
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:05:27.056229+00:00
-- url     : https://prove2.me/theorems/fd6b27cb-9118-4c4c-aae2-8cd3cffea3e6
-- title:
--   OBdd: reduced var dependent
-- statement:
--   The OBdd construction uses the reduced var dependent property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Basic.lean#L1364-L1402
-- source:
--   https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Basic.lean#L1364-L1402

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

theorem OBdd.reduced_var_dependent {O : OBdd n m} {p : Fin n} :
    O.Reduced → (∀ i : Fin p, Nary.IndependentOf (O.evaluate) ⟨i.1, by omega⟩) → p.1 ≤ O.1.var.1 := by sorry
