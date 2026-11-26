-- Prove2me | Theorems.Thm_LeanPool_K5MinorFreeChoosability_cliqueMinorFree_five_of_isPlanar
-- name    : LeanPool.K5MinorFreeChoosability.cliqueMinorFree_five_of_isPlanar
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T02:23:16.352461+00:00
-- url     : https://prove2.me/theorems/41aa78e2-0e90-4eed-a95a-edc32ee8bb89
-- title:
--   K5 Minor Free Choosability: clique Minor Free five of is Planar
-- statement:
--   A finite planar graph has no `K_5` minor.
--
--   Source: https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/LeanPool/K5MinorFreeChoosability/Planar/Nonplanar.lean#L200-L201
-- source:
--   https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/LeanPool/K5MinorFreeChoosability/Planar/Nonplanar.lean#L200-L201

module
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Planar_MinorClosed
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Planar_Nonplanar
set_option autoImplicit true
@[expose] public section
public section
open LeanPool LeanPool.K5MinorFreeChoosability
open Equiv Equiv.Perm
variable {V : Type*} {G : SimpleGraph V}

theorem LeanPool.K5MinorFreeChoosability.cliqueMinorFree_five_of_isPlanar [Finite V] (hG : IsPlanar G) : CliqueMinorFree G 5 := by sorry
