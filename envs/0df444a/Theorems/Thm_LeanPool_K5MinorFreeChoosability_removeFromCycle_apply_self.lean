-- Prove2me | Theorems.Thm_LeanPool_K5MinorFreeChoosability_removeFromCycle_apply_self
-- name    : LeanPool.K5MinorFreeChoosability.removeFromCycle_apply_self
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:11:23.768141+00:00
-- url     : https://prove2.me/theorems/0d2a9fda-8ae0-5e45-a2f1-6829cd8087f9
-- title:
--   K5 Minor Free Choosability: remove From Cycle apply self
-- statement:
--   The K5 Minor Free Choosability construction uses the remove From Cycle apply self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/LeanPool/K5MinorFreeChoosability/Planar/Orbits.lean#L421-L422
-- source:
--   https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/LeanPool/K5MinorFreeChoosability/Planar/Orbits.lean#L421-L422

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

theorem LeanPool.K5MinorFreeChoosability.removeFromCycle_apply_self (π : Perm α) (z : α) : removeFromCycle π z z = z := by sorry
