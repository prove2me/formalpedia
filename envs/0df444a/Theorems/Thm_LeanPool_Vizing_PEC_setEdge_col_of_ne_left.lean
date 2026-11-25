-- Prove2me | Theorems.Thm_LeanPool_Vizing_PEC_setEdge_col_of_ne_left
-- name    : LeanPool.Vizing.PEC.setEdge_col_of_ne_left
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T00:46:44.672226+00:00
-- url     : https://prove2.me/theorems/faad94b9-5671-49ef-b717-f1e95578833b
-- title:
--   PEC: set Edge col of ne left
-- statement:
--   The PEC construction uses the set Edge col of ne left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/galvin-dinitz/blob/84dcda4c2a760f2b52b7e813affe7e6968f8bfce/LeanPool/Vizing/Basic.lean#L158-L161
-- source:
--   https://github.com/jtraverso/galvin-dinitz/blob/84dcda4c2a760f2b52b7e813affe7e6968f8bfce/LeanPool/Vizing/Basic.lean#L158-L161

module
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Tactic.Choose
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Tauto
public import Definitions.Def_LeanPool_Vizing_Basic
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open LeanPool LeanPool.Vizing
variable {V : Type*} [DecidableEq V] {C : Type*}
open LeanPool.Vizing.PEC
variable {G : SimpleGraph V}

theorem LeanPool.Vizing.PEC.setEdge_col_of_ne_left (c : PEC G C) {x y : V} (γ : C) (hadj : G.Adj x y)
    (hx : c.IsFree x γ) (hy : c.IsFree y γ) {w : V} (hwx : w ≠ x) (hwy : w ≠ y) (u : V) :
    (c.setEdge γ hadj hx hy).col w u = c.col w u := by sorry
