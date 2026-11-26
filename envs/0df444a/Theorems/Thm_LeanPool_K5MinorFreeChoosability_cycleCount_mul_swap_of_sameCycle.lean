-- Prove2me | Theorems.Thm_LeanPool_K5MinorFreeChoosability_cycleCount_mul_swap_of_sameCycle
-- name    : LeanPool.K5MinorFreeChoosability.cycleCount_mul_swap_of_sameCycle
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:13:38.680427+00:00
-- url     : https://prove2.me/theorems/3344353f-8832-4c6e-a5a6-556c8c5dfadb
-- title:
--   K5 Minor Free Choosability: cycle Count mul swap of same Cycle
-- statement:
--   Splitting a cycle: if `x ≠ y` lie in the same cycle of `π`, then `π * swap x y` has one
--   more cycle.
--
--   Source: https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/LeanPool/K5MinorFreeChoosability/Planar/Orbits.lean#L356-L371
-- source:
--   https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/LeanPool/K5MinorFreeChoosability/Planar/Orbits.lean#L356-L371

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

theorem LeanPool.K5MinorFreeChoosability.cycleCount_mul_swap_of_sameCycle [Finite α] {π : Perm α} {x y : α} (hne : x ≠ y)
    (h : SameCycle π x y) : cycleCount (π * swap x y) = cycleCount π + 1 := by sorry
