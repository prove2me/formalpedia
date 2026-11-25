-- Prove2me | Theorems.Thm_LeanPool_Vizing_PEC_updFun_left
-- name    : LeanPool.Vizing.PEC.updFun_left
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T00:38:00.348513+00:00
-- url     : https://prove2.me/theorems/152d728d-e417-48c6-832e-5d4e3357e209
-- title:
--   PEC: upd Fun left
-- statement:
--   The PEC construction uses the upd Fun left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/galvin-dinitz/blob/84dcda4c2a760f2b52b7e813affe7e6968f8bfce/LeanPool/Vizing/Basic.lean#L97-L98
-- source:
--   https://github.com/jtraverso/galvin-dinitz/blob/84dcda4c2a760f2b52b7e813affe7e6968f8bfce/LeanPool/Vizing/Basic.lean#L97-L98

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

theorem LeanPool.Vizing.PEC.updFun_left {f : V → V → Option C} {x y : V} (o : Option C) :
    updFun f x y o x y = o := by sorry
