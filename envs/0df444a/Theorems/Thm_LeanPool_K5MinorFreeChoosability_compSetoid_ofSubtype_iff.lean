-- Prove2me | Theorems.Thm_LeanPool_K5MinorFreeChoosability_compSetoid_ofSubtype_iff
-- name    : LeanPool.K5MinorFreeChoosability.compSetoid_ofSubtype_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:16:37.119548+00:00
-- url     : https://prove2.me/theorems/fc30d77b-731f-5110-b64e-19b4966b1648
-- title:
--   K5 Minor Free Choosability: comp Setoid of Subtype iff
-- statement:
--   The K5 Minor Free Choosability construction uses the comp Setoid of Subtype iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/LeanPool/K5MinorFreeChoosability/Planar/Hypermap.lean#L313-L346
-- source:
--   https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/LeanPool/K5MinorFreeChoosability/Planar/Hypermap.lean#L313-L346

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

theorem LeanPool.K5MinorFreeChoosability.compSetoid_ofSubtype_iff (σ α : Perm (Subtype p)) (a b : Subtype p) :
    compSetoid σ α a b ↔ compSetoid (ofSubtype σ) (ofSubtype α) a.1 b.1 := by sorry
