-- Prove2me | Theorems.Thm_LeanPool_K5MinorFreeChoosability_eulerDefect_ofSubtype
-- name    : LeanPool.K5MinorFreeChoosability.eulerDefect_ofSubtype
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:18:17.733972+00:00
-- url     : https://prove2.me/theorems/52393bd6-becf-5506-aaf3-bdf4808edeb5
-- title:
--   K5 Minor Free Choosability: euler Defect of Subtype
-- statement:
--   Adding darts fixed by both permutations does not change the defect.
--
--   Source: https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/LeanPool/K5MinorFreeChoosability/Planar/Hypermap.lean#L371-L383
-- source:
--   https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/LeanPool/K5MinorFreeChoosability/Planar/Hypermap.lean#L371-L383

module
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Planar_Orbits
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Planar_Hypermap
set_option autoImplicit true
@[expose] public section
public section
open LeanPool LeanPool.K5MinorFreeChoosability
open Equiv Equiv.Perm
variable {D : Type*}
variable (p : D → Prop) [DecidablePred p]

theorem LeanPool.K5MinorFreeChoosability.eulerDefect_ofSubtype [Finite D] (σ α : Perm (Subtype p)) :
    eulerDefect (ofSubtype σ) (ofSubtype α) = eulerDefect σ α := by sorry
