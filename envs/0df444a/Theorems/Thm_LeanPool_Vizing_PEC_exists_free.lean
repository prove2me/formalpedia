-- Prove2me | Theorems.Thm_LeanPool_Vizing_PEC_exists_free
-- name    : LeanPool.Vizing.PEC.exists_free
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T00:56:13.034851+00:00
-- url     : https://prove2.me/theorems/4654a564-ae21-4be8-a911-d633ff7bb223
-- title:
--   PEC: exists free
-- statement:
--   At every vertex there is a free colour, provided there are more colours than the maximum
--   degree.
--
--   Source: https://github.com/jtraverso/galvin-dinitz/blob/84dcda4c2a760f2b52b7e813affe7e6968f8bfce/LeanPool/Vizing/Basic.lean#L70-L86
-- source:
--   https://github.com/jtraverso/galvin-dinitz/blob/84dcda4c2a760f2b52b7e813affe7e6968f8bfce/LeanPool/Vizing/Basic.lean#L70-L86

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
omit [DecidableEq V]

theorem LeanPool.Vizing.PEC.exists_free [Fintype V] [Fintype C] [DecidableRel G.Adj] (c : PEC G C)
    (hcard : G.maxDegree < Fintype.card C)
    (v : V) : ∃ γ, c.IsFree v γ := by sorry
