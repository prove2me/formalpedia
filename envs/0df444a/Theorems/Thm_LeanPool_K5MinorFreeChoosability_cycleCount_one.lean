-- Prove2me | Theorems.Thm_LeanPool_K5MinorFreeChoosability_cycleCount_one
-- name    : LeanPool.K5MinorFreeChoosability.cycleCount_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:13:49.993412+00:00
-- url     : https://prove2.me/theorems/2f96c0f8-a51b-4397-ad8b-5cc70fcdf195
-- title:
--   K5 Minor Free Choosability: cycle Count one
-- statement:
--   The identity permutation has `|α|` cycles.
--
--   Source: https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/LeanPool/K5MinorFreeChoosability/Planar/Orbits.lean#L402-L415
-- source:
--   https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/LeanPool/K5MinorFreeChoosability/Planar/Orbits.lean#L402-L415

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

theorem LeanPool.K5MinorFreeChoosability.cycleCount_one : cycleCount (1 : Perm α) = Nat.card α := by sorry
