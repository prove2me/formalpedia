-- Prove2me | Theorems.Thm_LeanPool_K5MinorFreeChoosability_sameCycle_removeFromCycle
-- name    : LeanPool.K5MinorFreeChoosability.sameCycle_removeFromCycle
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:14:07.616113+00:00
-- url     : https://prove2.me/theorems/7081f8d5-d7b0-4bdc-8c6b-69e727b6630c
-- title:
--   K5 Minor Free Choosability: same Cycle remove From Cycle
-- statement:
--   Removing `z` keeps the cycle relation among the other elements.
--
--   Source: https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/LeanPool/K5MinorFreeChoosability/Planar/Orbits.lean#L435-L443
-- source:
--   https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/LeanPool/K5MinorFreeChoosability/Planar/Orbits.lean#L435-L443

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

theorem LeanPool.K5MinorFreeChoosability.sameCycle_removeFromCycle {π : Perm α} {z u v : α} (hu : u ≠ z)
    (hv : v ≠ z) (h : SameCycle π u v) : SameCycle (removeFromCycle π z) u v := by sorry
