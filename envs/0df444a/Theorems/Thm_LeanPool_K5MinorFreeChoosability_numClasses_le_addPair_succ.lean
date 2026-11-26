-- Prove2me | Theorems.Thm_LeanPool_K5MinorFreeChoosability_numClasses_le_addPair_succ
-- name    : LeanPool.K5MinorFreeChoosability.numClasses_le_addPair_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:13:23.384296+00:00
-- url     : https://prove2.me/theorems/9000389e-b450-4118-b291-ade6e11ecc89
-- title:
--   K5 Minor Free Choosability: num Classes le add Pair succ
-- statement:
--   Adjoining one pair lowers the number of classes by at most one.
--
--   Source: https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/LeanPool/K5MinorFreeChoosability/Planar/Orbits.lean#L104-L117
-- source:
--   https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/LeanPool/K5MinorFreeChoosability/Planar/Orbits.lean#L104-L117

module
public import Mathlib
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Planar_Orbits
set_option autoImplicit true
@[expose] public section
public section
open LeanPool LeanPool.K5MinorFreeChoosability
open Equiv Equiv.Perm
variable {α : Type*}

theorem LeanPool.K5MinorFreeChoosability.numClasses_le_addPair_succ [Finite α] (s : Setoid α) (x y : α) :
    numClasses s ≤ numClasses (addPairSetoid s x y) + 1 := by sorry
