-- Prove2me | Theorems.Thm_LeanPool_K5MinorFreeChoosability_not_isPlanar_K5
-- name    : LeanPool.K5MinorFreeChoosability.not_isPlanar_K5
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T02:22:49.008939+00:00
-- url     : https://prove2.me/theorems/25e6d0b5-ee8b-5b7a-90e4-476f8af6dd5f
-- title:
--   K5 Minor Free Choosability: not is Planar K5
-- statement:
--   `K_5` is not planar.
--
--   Source: https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/LeanPool/K5MinorFreeChoosability/Planar/Nonplanar.lean#L151-L172
-- source:
--   https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/LeanPool/K5MinorFreeChoosability/Planar/Nonplanar.lean#L151-L172

module
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Planar_MinorClosed
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Planar_Nonplanar
set_option autoImplicit true
@[expose] public section
public section
open LeanPool LeanPool.K5MinorFreeChoosability
open Equiv Equiv.Perm
variable {V : Type*} {G : SimpleGraph V}

theorem LeanPool.K5MinorFreeChoosability.not_isPlanar_K5 : ¬ IsPlanar (⊤ : SimpleGraph (Fin 5)) := by sorry
