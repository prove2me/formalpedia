-- Prove2me | Theorems.Thm_LeanPool_K5MinorFreeChoosability_numClasses_addPair_of_not
-- name    : LeanPool.K5MinorFreeChoosability.numClasses_addPair_of_not
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:10:46.288854+00:00
-- url     : https://prove2.me/theorems/b44e017a-92b2-5dab-bbd6-8dca0f3e1297
-- title:
--   K5 Minor Free Choosability: num Classes add Pair of not
-- statement:
--   Adjoining a pair from two different classes lowers the number of classes by exactly
--   one.
--
--   Source: https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/LeanPool/K5MinorFreeChoosability/Planar/Orbits.lean#L121-L149
-- source:
--   https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/LeanPool/K5MinorFreeChoosability/Planar/Orbits.lean#L121-L149

module
public import Mathlib
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Planar_Orbits
set_option autoImplicit true
@[expose] public section
public section
open LeanPool LeanPool.K5MinorFreeChoosability
open Equiv Equiv.Perm
variable {α : Type*}

theorem LeanPool.K5MinorFreeChoosability.numClasses_addPair_of_not [Finite α] {s : Setoid α} {x y : α} (hxy : ¬ s x y) :
    numClasses s = numClasses (addPairSetoid s x y) + 1 := by sorry
