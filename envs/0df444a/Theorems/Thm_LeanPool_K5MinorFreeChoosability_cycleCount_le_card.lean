-- Prove2me | Theorems.Thm_LeanPool_K5MinorFreeChoosability_cycleCount_le_card
-- name    : LeanPool.K5MinorFreeChoosability.cycleCount_le_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:13:38.654424+00:00
-- url     : https://prove2.me/theorems/8d9d1a66-643f-556c-abb7-dfdcd2627e5b
-- title:
--   K5 Minor Free Choosability: cycle Count le card
-- statement:
--   The K5 Minor Free Choosability construction uses the cycle Count le card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/LeanPool/K5MinorFreeChoosability/Planar/Orbits.lean#L397-L398
-- source:
--   https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/LeanPool/K5MinorFreeChoosability/Planar/Orbits.lean#L397-L398

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

theorem LeanPool.K5MinorFreeChoosability.cycleCount_le_card [Finite α] (π : Perm α) : cycleCount π ≤ Nat.card α := by sorry
