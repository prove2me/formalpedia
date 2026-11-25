-- Prove2me | Theorems.Thm_LeanPool_Vizing_PEC_updFun_right
-- name    : LeanPool.Vizing.PEC.updFun_right
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T00:41:23.849616+00:00
-- url     : https://prove2.me/theorems/d7a2474b-bc0f-4614-98d8-c2a850e53571
-- title:
--   PEC: upd Fun right
-- statement:
--   The PEC construction uses the upd Fun right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/galvin-dinitz/blob/84dcda4c2a760f2b52b7e813affe7e6968f8bfce/LeanPool/Vizing/Basic.lean#L100-L101
-- source:
--   https://github.com/jtraverso/galvin-dinitz/blob/84dcda4c2a760f2b52b7e813affe7e6968f8bfce/LeanPool/Vizing/Basic.lean#L100-L101

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

theorem LeanPool.Vizing.PEC.updFun_right {f : V → V → Option C} {x y : V} (o : Option C) :
    updFun f x y o y x = o := by sorry
