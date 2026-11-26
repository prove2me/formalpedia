-- Prove2me | Theorems.Thm_LeanPool_K5MinorFreeChoosability_compSetoid_ofSubtype_out
-- name    : LeanPool.K5MinorFreeChoosability.compSetoid_ofSubtype_out
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:16:38.562182+00:00
-- url     : https://prove2.me/theorems/ed54a35c-f143-5cee-aa58-d8e31ec79262
-- title:
--   K5 Minor Free Choosability: comp Setoid of Subtype out
-- statement:
--   The K5 Minor Free Choosability construction uses the comp Setoid of Subtype out property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/LeanPool/K5MinorFreeChoosability/Planar/Hypermap.lean#L348-L368
-- source:
--   https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/LeanPool/K5MinorFreeChoosability/Planar/Hypermap.lean#L348-L368

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

theorem LeanPool.K5MinorFreeChoosability.compSetoid_ofSubtype_out (σ α : Perm (Subtype p)) (u v : D) (hu : ¬ p u)
    (h : compSetoid (ofSubtype σ) (ofSubtype α) u v) : u = v := by sorry
