-- Prove2me | Theorems.Thm_LeanPool_K5MinorFreeChoosability_numClasses_le_of_le
-- name    : LeanPool.K5MinorFreeChoosability.numClasses_le_of_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:13:02.896155+00:00
-- url     : https://prove2.me/theorems/90b2ac01-b21a-5889-887e-a84cdeb99e63
-- title:
--   K5 Minor Free Choosability: num Classes le of le
-- statement:
--   A coarser relation has at most as many classes.
--
--   Source: https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/LeanPool/K5MinorFreeChoosability/Planar/Orbits.lean#L71-L77
-- source:
--   https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/LeanPool/K5MinorFreeChoosability/Planar/Orbits.lean#L71-L77

module
public import Mathlib
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Planar_Orbits
set_option autoImplicit true
@[expose] public section
public section
open LeanPool LeanPool.K5MinorFreeChoosability
open Equiv Equiv.Perm
variable {α : Type*}

theorem LeanPool.K5MinorFreeChoosability.numClasses_le_of_le [Finite α] {s t : Setoid α} (h : ∀ a b, s a b → t a b) :
    numClasses t ≤ numClasses s := by sorry
