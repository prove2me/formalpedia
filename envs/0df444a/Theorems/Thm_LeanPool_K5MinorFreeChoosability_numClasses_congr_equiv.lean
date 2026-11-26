-- Prove2me | Theorems.Thm_LeanPool_K5MinorFreeChoosability_numClasses_congr_equiv
-- name    : LeanPool.K5MinorFreeChoosability.numClasses_congr_equiv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:13:10.252433+00:00
-- url     : https://prove2.me/theorems/2ce37bde-13b7-5d30-a39d-c4db6907bb9f
-- title:
--   K5 Minor Free Choosability: num Classes congr equiv
-- statement:
--   Transport of the number of classes along an equivalence of types.
--
--   Source: https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/LeanPool/K5MinorFreeChoosability/Planar/Orbits.lean#L83-L85
-- source:
--   https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/LeanPool/K5MinorFreeChoosability/Planar/Orbits.lean#L83-L85

module
public import Mathlib
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Planar_Orbits
set_option autoImplicit true
@[expose] public section
public section
open LeanPool LeanPool.K5MinorFreeChoosability
open Equiv Equiv.Perm
variable {α : Type*}

theorem LeanPool.K5MinorFreeChoosability.numClasses_congr_equiv {β : Type*} {s : Setoid α} {t : Setoid β} (e : α ≃ β)
    (h : ∀ a b, s a b ↔ t (e a) (e b)) : numClasses s = numClasses t := by sorry
