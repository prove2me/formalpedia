-- Prove2me | Theorems.Thm_LeanPool_K5MinorFreeChoosability_eulerDefect_nonneg
-- name    : LeanPool.K5MinorFreeChoosability.eulerDefect_nonneg
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T02:18:01.445722+00:00
-- url     : https://prove2.me/theorems/a3868358-3951-4ce5-b4d9-3bdabc21da9f
-- title:
--   K5 Minor Free Choosability: euler Defect nonneg
-- statement:
--   **Euler's inequality** for hypermaps: the defect (twice the genus) is nonnegative.
--
--   Source: https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/LeanPool/K5MinorFreeChoosability/Planar/Hypermap.lean#L224-L239
-- source:
--   https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/LeanPool/K5MinorFreeChoosability/Planar/Hypermap.lean#L224-L239

module
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Planar_Orbits
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Planar_Hypermap
set_option autoImplicit true
@[expose] public section
public section
open LeanPool LeanPool.K5MinorFreeChoosability
open Equiv Equiv.Perm
variable {D : Type*}

theorem LeanPool.K5MinorFreeChoosability.eulerDefect_nonneg [Finite D] (σ α : Perm D) : 0 ≤ eulerDefect σ α := by sorry
