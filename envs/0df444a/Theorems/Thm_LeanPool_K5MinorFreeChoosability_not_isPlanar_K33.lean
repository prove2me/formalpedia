-- Prove2me | Theorems.Thm_LeanPool_K5MinorFreeChoosability_not_isPlanar_K33
-- name    : LeanPool.K5MinorFreeChoosability.not_isPlanar_K33
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T02:23:18.03209+00:00
-- url     : https://prove2.me/theorems/dc8c38f5-b239-49f9-a94a-33dd23eec774
-- title:
--   K5 Minor Free Choosability: not is Planar K33
-- statement:
--   `K_{3,3}` is not planar.
--
--   Source: https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/LeanPool/K5MinorFreeChoosability/Planar/Nonplanar.lean#L175-L197
-- source:
--   https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/LeanPool/K5MinorFreeChoosability/Planar/Nonplanar.lean#L175-L197

module
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Planar_MinorClosed
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Planar_Nonplanar
set_option autoImplicit true
@[expose] public section
public section
open LeanPool LeanPool.K5MinorFreeChoosability
open Equiv Equiv.Perm
variable {V : Type*} {G : SimpleGraph V}

theorem LeanPool.K5MinorFreeChoosability.not_isPlanar_K33 : ¬ IsPlanar K33 := by sorry
