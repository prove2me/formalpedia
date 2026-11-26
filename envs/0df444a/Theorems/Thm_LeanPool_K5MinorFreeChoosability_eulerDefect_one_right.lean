-- Prove2me | Theorems.Thm_LeanPool_K5MinorFreeChoosability_eulerDefect_one_right
-- name    : LeanPool.K5MinorFreeChoosability.eulerDefect_one_right
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:16:14.268269+00:00
-- url     : https://prove2.me/theorems/ff3f4915-4000-4dc4-a539-0506b203ead3
-- title:
--   K5 Minor Free Choosability: euler Defect one right
-- statement:
--   With `α = 1` the defect vanishes.
--
--   Source: https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/LeanPool/K5MinorFreeChoosability/Planar/Hypermap.lean#L214-L221
-- source:
--   https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/LeanPool/K5MinorFreeChoosability/Planar/Hypermap.lean#L214-L221

module
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Planar_Orbits
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Planar_Hypermap
set_option autoImplicit true
@[expose] public section
public section
open LeanPool LeanPool.K5MinorFreeChoosability
open Equiv Equiv.Perm
variable {D : Type*}

theorem LeanPool.K5MinorFreeChoosability.eulerDefect_one_right [Finite D] (σ : Perm D) : eulerDefect σ 1 = 0 := by sorry
