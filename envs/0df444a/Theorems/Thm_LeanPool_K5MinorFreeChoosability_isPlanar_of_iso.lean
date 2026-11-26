-- Prove2me | Theorems.Thm_LeanPool_K5MinorFreeChoosability_isPlanar_of_iso
-- name    : LeanPool.K5MinorFreeChoosability.isPlanar_of_iso
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T02:26:33.157896+00:00
-- url     : https://prove2.me/theorems/b37c1ef0-1d08-586e-ad82-52de8d11a120
-- title:
--   K5 Minor Free Choosability: is Planar of iso
-- statement:
--   Planarity is invariant under isomorphism.
--
--   Source: https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/LeanPool/K5MinorFreeChoosability/Planar/MinorClosed.lean#L448-L449
-- source:
--   https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/LeanPool/K5MinorFreeChoosability/Planar/MinorClosed.lean#L448-L449

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

theorem LeanPool.K5MinorFreeChoosability.isPlanar_of_iso [Finite V] (hG : IsPlanar G) (e : H ≃g G) : IsPlanar H := by sorry
