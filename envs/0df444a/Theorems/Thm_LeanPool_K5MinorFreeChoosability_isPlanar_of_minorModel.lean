-- Prove2me | Theorems.Thm_LeanPool_K5MinorFreeChoosability_isPlanar_of_minorModel
-- name    : LeanPool.K5MinorFreeChoosability.isPlanar_of_minorModel
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T02:18:59.252797+00:00
-- url     : https://prove2.me/theorems/5172a52f-9754-5461-a1f6-71e64fc4ad80
-- title:
--   K5 Minor Free Choosability: is Planar of minor Model
-- statement:
--   **Planarity is minor-closed**: a minor of a finite planar graph is planar.
--
--   Source: https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/LeanPool/K5MinorFreeChoosability/Planar/MinorClosed.lean#L338-L445
-- source:
--   https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/LeanPool/K5MinorFreeChoosability/Planar/MinorClosed.lean#L338-L445

module
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Planar_Embedding
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Planar_MinorModel
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Planar_MinorClosed
set_option autoImplicit true
@[expose] public section
public section
open LeanPool LeanPool.K5MinorFreeChoosability
open Equiv Equiv.Perm
variable {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}

theorem LeanPool.K5MinorFreeChoosability.isPlanar_of_minorModel [Finite V] (hG : IsPlanar G) (M : MinorModel G H) :
    IsPlanar H := by sorry
