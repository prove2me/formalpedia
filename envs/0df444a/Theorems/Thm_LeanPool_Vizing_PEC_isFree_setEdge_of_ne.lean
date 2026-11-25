-- Prove2me | Theorems.Thm_LeanPool_Vizing_PEC_isFree_setEdge_of_ne
-- name    : LeanPool.Vizing.PEC.isFree_setEdge_of_ne
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T00:57:58.767933+00:00
-- url     : https://prove2.me/theorems/fa25104d-0f8a-4b3a-8442-4efa364a5e8f
-- title:
--   PEC: is Free set Edge of ne
-- statement:
--   The PEC construction uses the is Free set Edge of ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/galvin-dinitz/blob/84dcda4c2a760f2b52b7e813affe7e6968f8bfce/LeanPool/Vizing/Basic.lean#L163-L169
-- source:
--   https://github.com/jtraverso/galvin-dinitz/blob/84dcda4c2a760f2b52b7e813affe7e6968f8bfce/LeanPool/Vizing/Basic.lean#L163-L169

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

theorem LeanPool.Vizing.PEC.isFree_setEdge_of_ne (c : PEC G C) {x y : V} (γ : C) (hadj : G.Adj x y)
    (hx : c.IsFree x γ) (hy : c.IsFree y γ) {w : V} (hwx : w ≠ x) (hwy : w ≠ y) (δ : C) :
    (c.setEdge γ hadj hx hy).IsFree w δ ↔ c.IsFree w δ := by sorry
