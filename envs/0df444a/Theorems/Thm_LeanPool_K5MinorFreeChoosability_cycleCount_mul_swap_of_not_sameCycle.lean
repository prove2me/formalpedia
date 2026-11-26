-- Prove2me | Theorems.Thm_LeanPool_K5MinorFreeChoosability_cycleCount_mul_swap_of_not_sameCycle
-- name    : LeanPool.K5MinorFreeChoosability.cycleCount_mul_swap_of_not_sameCycle
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:13:47.473658+00:00
-- url     : https://prove2.me/theorems/6e5066ff-3f8b-44dc-9e10-7873f00ae7b7
-- title:
--   K5 Minor Free Choosability: cycle Count mul swap of not same Cycle
-- statement:
--   Merging two cycles: if `x` and `y` lie in different cycles of `π`, then `π * swap x y`
--   has one fewer cycle.
--
--   Source: https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/LeanPool/K5MinorFreeChoosability/Planar/Orbits.lean#L375-L394
-- source:
--   https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/LeanPool/K5MinorFreeChoosability/Planar/Orbits.lean#L375-L394

module
public import Mathlib
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Planar_Orbits
set_option autoImplicit true
@[expose] public section
public section
open LeanPool LeanPool.K5MinorFreeChoosability
open Equiv Equiv.Perm
variable {α : Type*}
variable [DecidableEq α]

theorem LeanPool.K5MinorFreeChoosability.cycleCount_mul_swap_of_not_sameCycle [Finite α] {π : Perm α} {x y : α}
    (h : ¬ SameCycle π x y) : cycleCount (π * swap x y) + 1 = cycleCount π := by sorry
