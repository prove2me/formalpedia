-- Prove2me | Theorems.Thm_LeanPool_K5MinorFreeChoosability_mulSwap_mulSwap
-- name    : LeanPool.K5MinorFreeChoosability.mulSwap_mulSwap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:11:03.46004+00:00
-- url     : https://prove2.me/theorems/d8eaf061-5a76-4174-91f1-2efd2f737e20
-- title:
--   K5 Minor Free Choosability: mul Swap mul Swap
-- statement:
--   The K5 Minor Free Choosability construction uses the mul Swap mul Swap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/LeanPool/K5MinorFreeChoosability/Planar/Orbits.lean#L278-L279
-- source:
--   https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/LeanPool/K5MinorFreeChoosability/Planar/Orbits.lean#L278-L279

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

theorem LeanPool.K5MinorFreeChoosability.mulSwap_mulSwap (π : Perm α) (x y : α) : π * swap x y * swap x y = π := by sorry
