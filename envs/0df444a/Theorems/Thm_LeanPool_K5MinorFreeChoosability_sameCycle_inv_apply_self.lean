-- Prove2me | Theorems.Thm_LeanPool_K5MinorFreeChoosability_sameCycle_inv_apply_self
-- name    : LeanPool.K5MinorFreeChoosability.sameCycle_inv_apply_self
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:14:17.357808+00:00
-- url     : https://prove2.me/theorems/7afbe8fb-ee58-4288-a8cd-40e3508f8ced
-- title:
--   K5 Minor Free Choosability: same Cycle inv apply self
-- statement:
--   The K5 Minor Free Choosability construction uses the same Cycle inv apply self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/LeanPool/K5MinorFreeChoosability/Planar/Orbits.lean#L451-L452
-- source:
--   https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/LeanPool/K5MinorFreeChoosability/Planar/Orbits.lean#L451-L452

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
omit [DecidableEq α]

theorem LeanPool.K5MinorFreeChoosability.sameCycle_inv_apply_self (π : Perm α) (z : α) : SameCycle π (π⁻¹ z) z := by sorry
