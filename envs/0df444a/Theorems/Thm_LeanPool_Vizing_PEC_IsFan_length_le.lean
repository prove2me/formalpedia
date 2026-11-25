-- Prove2me | Theorems.Thm_LeanPool_Vizing_PEC_IsFan_length_le
-- name    : LeanPool.Vizing.PEC.IsFan.length_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:02:37.1277+00:00
-- url     : https://prove2.me/theorems/d86a44ee-0937-480d-88e4-42f2a84f4a80
-- title:
--   Is Fan: length le
-- statement:
--   A fan has at most `Fintype.card V` vertices.
--
--   Source: https://github.com/jtraverso/galvin-dinitz/blob/84dcda4c2a760f2b52b7e813affe7e6968f8bfce/LeanPool/Vizing/Fan.lean#L40-L49
-- source:
--   https://github.com/jtraverso/galvin-dinitz/blob/84dcda4c2a760f2b52b7e813affe7e6968f8bfce/LeanPool/Vizing/Fan.lean#L40-L49

module
public import Definitions.Def_LeanPool_Vizing_Kempe
public import Definitions.Def_LeanPool_Vizing_Fan
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open LeanPool LeanPool.Vizing
open LeanPool.Vizing.PEC
variable {V : Type*} [Fintype V] [DecidableEq V] {C : Type*} [DecidableEq C]
  {G : SimpleGraph V}
omit [DecidableEq V] [DecidableEq C]

theorem LeanPool.Vizing.PEC.IsFan.length_le {c : PEC G C} {x y : V} {n : ℕ} {f : ℕ → V} (h : c.IsFan x y n f) :
    n ≤ Fintype.card V := by sorry
