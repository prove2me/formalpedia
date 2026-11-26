-- Prove2me | Theorems.Thm_LeanPool_K5MinorFreeChoosability_removeFromCycle_eq_of_fixed
-- name    : LeanPool.K5MinorFreeChoosability.removeFromCycle_eq_of_fixed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:14:02.966109+00:00
-- url     : https://prove2.me/theorems/ff652a51-34f7-5580-bd66-d0455ac2ba0a
-- title:
--   K5 Minor Free Choosability: remove From Cycle eq of fixed
-- statement:
--   The K5 Minor Free Choosability construction uses the remove From Cycle eq of fixed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/LeanPool/K5MinorFreeChoosability/Planar/Orbits.lean#L445-L448
-- source:
--   https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/LeanPool/K5MinorFreeChoosability/Planar/Orbits.lean#L445-L448

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

theorem LeanPool.K5MinorFreeChoosability.removeFromCycle_eq_of_fixed {π : Perm α} {z : α} (hz : π⁻¹ z = z) :
    removeFromCycle π z = π := by sorry
