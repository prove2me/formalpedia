-- Prove2me | Theorems.Thm_LeanPool_Vizing_PEC_updFun_of_ne
-- name    : LeanPool.Vizing.PEC.updFun_of_ne
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T00:46:15.135582+00:00
-- url     : https://prove2.me/theorems/4277e740-40b6-433d-8a91-70ef87a78ba5
-- title:
--   PEC: upd Fun of ne
-- statement:
--   The PEC construction uses the upd Fun of ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/galvin-dinitz/blob/84dcda4c2a760f2b52b7e813affe7e6968f8bfce/LeanPool/Vizing/Basic.lean#L94-L95
-- source:
--   https://github.com/jtraverso/galvin-dinitz/blob/84dcda4c2a760f2b52b7e813affe7e6968f8bfce/LeanPool/Vizing/Basic.lean#L94-L95

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

theorem LeanPool.Vizing.PEC.updFun_of_ne {f : V → V → Option C} {x y u v : V} (o : Option C)
    (h : ¬((u = x ∧ v = y) ∨ (u = y ∧ v = x))) : updFun f x y o u v = f u v := by sorry
