-- Prove2me | Theorems.Thm_LeanPool_K5MinorFreeChoosability_k33MinorFree_of_isPlanar
-- name    : LeanPool.K5MinorFreeChoosability.k33MinorFree_of_isPlanar
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T02:23:35.016397+00:00
-- url     : https://prove2.me/theorems/6f100942-9b3d-41f2-b56b-6243df453199
-- title:
--   K5 Minor Free Choosability: k33 Minor Free of is Planar
-- statement:
--   A finite planar graph has no `K_{3,3}` minor.
--
--   Source: https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/LeanPool/K5MinorFreeChoosability/Planar/Nonplanar.lean#L204-L205
-- source:
--   https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/LeanPool/K5MinorFreeChoosability/Planar/Nonplanar.lean#L204-L205

module
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Planar_MinorClosed
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Planar_Nonplanar
set_option autoImplicit true
@[expose] public section
public section
open LeanPool LeanPool.K5MinorFreeChoosability
open Equiv Equiv.Perm
variable {V : Type*} {G : SimpleGraph V}

theorem LeanPool.K5MinorFreeChoosability.k33MinorFree_of_isPlanar [Finite V] (hG : IsPlanar G) : K33MinorFree G := by sorry
