-- Prove2me | Theorems.Thm_OBdd_evaluate_cast
-- name    : OBdd.evaluate_cast
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:02:30.395545+00:00
-- url     : https://prove2.me/theorems/16d158e9-982c-49b5-8910-c433e7f6af2a
-- title:
--   OBdd: evaluate cast
-- statement:
--   The OBdd construction uses the evaluate cast property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Basic.lean#L319-L321
-- source:
--   https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Basic.lean#L319-L321

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

theorem OBdd.evaluate_cast {O : OBdd n m} (h : n = n') : (h ▸ O).evaluate I = O.evaluate (h ▸ I) := by sorry
