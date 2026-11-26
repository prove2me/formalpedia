-- Prove2me | Theorems.Thm_LeanPool_K5MinorFreeChoosability_isPlanar_of_edgeless
-- name    : LeanPool.K5MinorFreeChoosability.isPlanar_of_edgeless
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:20:53.81184+00:00
-- url     : https://prove2.me/theorems/c4496b3c-4d49-5109-9a3a-438f35c99a4a
-- title:
--   K5 Minor Free Choosability: is Planar of edgeless
-- statement:
--   A graph without edges is planar (with the empty rotation system).
--
--   Source: https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/LeanPool/K5MinorFreeChoosability/Planar/Embedding.lean#L146-L150
-- source:
--   https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/LeanPool/K5MinorFreeChoosability/Planar/Embedding.lean#L146-L150

module
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Planar_Hypermap
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Planar_Embedding
set_option autoImplicit true
@[expose] public section
public section
open LeanPool LeanPool.K5MinorFreeChoosability
open Equiv Equiv.Perm
variable {V : Type*} (G : SimpleGraph V)

theorem LeanPool.K5MinorFreeChoosability.isPlanar_of_edgeless [Finite V] (h : ∀ u v, ¬ G.Adj u v) : IsPlanar G := by sorry
