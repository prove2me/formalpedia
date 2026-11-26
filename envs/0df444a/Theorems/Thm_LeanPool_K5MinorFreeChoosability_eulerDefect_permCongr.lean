-- Prove2me | Theorems.Thm_LeanPool_K5MinorFreeChoosability_eulerDefect_permCongr
-- name    : LeanPool.K5MinorFreeChoosability.eulerDefect_permCongr
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T02:18:12.875979+00:00
-- url     : https://prove2.me/theorems/2e6187cc-8fb1-5426-8ac2-065568e99f3a
-- title:
--   K5 Minor Free Choosability: euler Defect perm Congr
-- statement:
--   The defect does not depend on the names of the darts.
--
--   Source: https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/LeanPool/K5MinorFreeChoosability/Planar/Hypermap.lean#L295-L299
-- source:
--   https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/LeanPool/K5MinorFreeChoosability/Planar/Hypermap.lean#L295-L299

module
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Planar_Orbits
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Planar_Hypermap
set_option autoImplicit true
@[expose] public section
public section
open LeanPool LeanPool.K5MinorFreeChoosability
open Equiv Equiv.Perm
variable {D : Type*}

theorem LeanPool.K5MinorFreeChoosability.eulerDefect_permCongr {D' : Type*} (e : D ≃ D') (σ α : Perm D) :
    eulerDefect (e.permCongr σ) (e.permCongr α) = eulerDefect σ α := by sorry
