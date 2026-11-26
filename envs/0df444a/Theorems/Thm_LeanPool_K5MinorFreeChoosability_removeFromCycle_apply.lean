-- Prove2me | Theorems.Thm_LeanPool_K5MinorFreeChoosability_removeFromCycle_apply
-- name    : LeanPool.K5MinorFreeChoosability.removeFromCycle_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:14:04.442328+00:00
-- url     : https://prove2.me/theorems/04d1a9ab-fdfc-4211-a525-0136dd7e7bae
-- title:
--   K5 Minor Free Choosability: remove From Cycle apply
-- statement:
--   The K5 Minor Free Choosability construction uses the remove From Cycle apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/LeanPool/K5MinorFreeChoosability/Planar/Orbits.lean#L424-L432
-- source:
--   https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/LeanPool/K5MinorFreeChoosability/Planar/Orbits.lean#L424-L432

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

theorem LeanPool.K5MinorFreeChoosability.removeFromCycle_apply (π : Perm α) {z u : α} (huz : u ≠ z) :
    removeFromCycle π z u = if π u = z then π z else π u := by sorry
