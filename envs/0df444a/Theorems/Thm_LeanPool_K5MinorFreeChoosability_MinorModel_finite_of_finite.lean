-- Prove2me | Theorems.Thm_LeanPool_K5MinorFreeChoosability_MinorModel_finite_of_finite
-- name    : LeanPool.K5MinorFreeChoosability.MinorModel.finite_of_finite
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:14:42.087216+00:00
-- url     : https://prove2.me/theorems/1e37159f-1883-4ce5-9330-392fa05513ce
-- title:
--   Minor Model: finite of finite
-- statement:
--   The vertex type of a minor of a finite graph is finite.
--
--   Source: https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/LeanPool/K5MinorFreeChoosability/Planar/MinorModel.lean#L101-L108
-- source:
--   https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/LeanPool/K5MinorFreeChoosability/Planar/MinorModel.lean#L101-L108

module
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Reach
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Planar_MinorModel
set_option autoImplicit true
@[expose] public section
public section
open LeanPool LeanPool.K5MinorFreeChoosability
variable {V W : Type*}
variable {G : SimpleGraph V} {k : ℕ}
open LeanPool.K5MinorFreeChoosability.MinorModel
variable {H : SimpleGraph W} (M : MinorModel G H)
include M

theorem LeanPool.K5MinorFreeChoosability.MinorModel.finite_of_finite [Finite V] : Finite W := by sorry
