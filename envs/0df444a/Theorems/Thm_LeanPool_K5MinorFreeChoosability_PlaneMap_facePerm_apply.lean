-- Prove2me | Theorems.Thm_LeanPool_K5MinorFreeChoosability_PlaneMap_facePerm_apply
-- name    : LeanPool.K5MinorFreeChoosability.PlaneMap.facePerm_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:20:18.26167+00:00
-- url     : https://prove2.me/theorems/afa1508f-b060-4a7d-b894-6a8d6d24cb3a
-- title:
--   Plane Map: face Perm apply
-- statement:
--   The Plane Map construction uses the face Perm apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/LeanPool/K5MinorFreeChoosability/Planar/Embedding.lean#L72-L72
-- source:
--   https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/LeanPool/K5MinorFreeChoosability/Planar/Embedding.lean#L72-L72

module
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Planar_Hypermap
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Planar_Embedding
set_option autoImplicit true
@[expose] public section
public section
open LeanPool LeanPool.K5MinorFreeChoosability
open Equiv Equiv.Perm
variable {V : Type*} (G : SimpleGraph V)
open LeanPool.K5MinorFreeChoosability.PlaneMap
variable {G} (M : PlaneMap G)

theorem LeanPool.K5MinorFreeChoosability.PlaneMap.facePerm_apply (d : G.Dart) : M.facePerm d = M.rot d.symm := by sorry
