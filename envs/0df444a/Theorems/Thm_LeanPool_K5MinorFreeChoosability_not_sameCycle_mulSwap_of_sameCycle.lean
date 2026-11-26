-- Prove2me | Theorems.Thm_LeanPool_K5MinorFreeChoosability_not_sameCycle_mulSwap_of_sameCycle
-- name    : LeanPool.K5MinorFreeChoosability.not_sameCycle_mulSwap_of_sameCycle
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:11:26.937958+00:00
-- url     : https://prove2.me/theorems/ec8b659c-6ff4-4b1a-9dd4-970803141f11
-- title:
--   K5 Minor Free Choosability: not same Cycle mul Swap of same Cycle
-- statement:
--   If `x ≠ y` lie in the same cycle of `π`, they lie in different cycles of
--   `π * swap x y`.
--
--   Source: https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/LeanPool/K5MinorFreeChoosability/Planar/Orbits.lean#L332-L352
-- source:
--   https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/LeanPool/K5MinorFreeChoosability/Planar/Orbits.lean#L332-L352

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

theorem LeanPool.K5MinorFreeChoosability.not_sameCycle_mulSwap_of_sameCycle [Finite α] {π : Perm α} {x y : α} (hne : x ≠ y)
    (h : SameCycle π x y) : ¬ SameCycle (π * swap x y) x y := by sorry
