-- Prove2me | Theorems.Thm_LeanPool_Vizing_PEC_setEdge_col
-- name    : LeanPool.Vizing.PEC.setEdge_col
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T00:38:01.647086+00:00
-- url     : https://prove2.me/theorems/3b448bd2-1564-464c-a906-b69e6497dd6b
-- title:
--   PEC: set Edge col
-- statement:
--   The PEC construction uses the set Edge col property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/galvin-dinitz/blob/84dcda4c2a760f2b52b7e813affe7e6968f8bfce/LeanPool/Vizing/Basic.lean#L154-L156
-- source:
--   https://github.com/jtraverso/galvin-dinitz/blob/84dcda4c2a760f2b52b7e813affe7e6968f8bfce/LeanPool/Vizing/Basic.lean#L154-L156

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

theorem LeanPool.Vizing.PEC.setEdge_col (c : PEC G C) {x y : V} (γ : C) (hadj : G.Adj x y)
    (hx : c.IsFree x γ) (hy : c.IsFree y γ) :
    (c.setEdge γ hadj hx hy).col = updFun c.col x y (some γ) := by sorry

attribute [defeq] LeanPool.Vizing.PEC.setEdge_col
