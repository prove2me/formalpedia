-- Prove2me | Theorems.Thm_OBdd_init_inductionOn
-- name    : OBdd.init_inductionOn
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T06:58:57.521187+00:00
-- url     : https://prove2.me/theorems/53377659-37cd-4864-b71b-cba1cf157451
-- title:
--   OBdd: init induction On
-- statement:
--   The OBdd construction uses the init induction On property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Basic.lean#L527-L551
-- source:
--   https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Basic.lean#L527-L551

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

theorem OBdd.init_inductionOn t {motive : OBdd n m → Prop}
    (base : (b : Bool) → motive ⟨{heap := t.1.heap, root := terminal b}, Ordered_of_terminal⟩)
    (step : (j : Fin m) →
            (hl : ({heap := t.1.heap, root := t.1.heap[j].low} : Bdd n m).Ordered) →
            motive ⟨{heap := t.1.heap, root := t.1.heap[j].low}, hl⟩ →
            (hh : ({heap := t.1.heap, root := t.1.heap[j].high} : Bdd n m).Ordered) →
            motive ⟨{heap := t.1.heap, root := t.1.heap[j].high}, hh⟩ →
            (h : ({heap := t.1.heap, root := node j} : Bdd n m).Ordered) →
            motive ⟨{heap := t.1.heap, root := node j}, h⟩)
    : motive t := by sorry
