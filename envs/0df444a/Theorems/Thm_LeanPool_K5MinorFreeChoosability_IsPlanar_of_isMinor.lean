-- Prove2me | Theorems.Thm_LeanPool_K5MinorFreeChoosability_IsPlanar_of_isMinor
-- name    : LeanPool.K5MinorFreeChoosability.IsPlanar.of_isMinor
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T02:26:42.120912+00:00
-- url     : https://prove2.me/theorems/6a991bfb-a1c0-4f31-a598-659cd1c0b3f3
-- title:
--   Is Planar: of is Minor
-- statement:
--   A minor of a planar graph is planar.
--
--   Source: https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/LeanPool/K5MinorFreeChoosability/Planar/MinorClosed.lean#L452-L453
-- source:
--   https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/LeanPool/K5MinorFreeChoosability/Planar/MinorClosed.lean#L452-L453

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

theorem LeanPool.K5MinorFreeChoosability.IsPlanar.of_isMinor [Finite V] (hG : IsPlanar G) (h : IsMinor H G) : IsPlanar H := by sorry
