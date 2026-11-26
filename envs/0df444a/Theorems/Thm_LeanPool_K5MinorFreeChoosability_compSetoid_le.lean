-- Prove2me | Theorems.Thm_LeanPool_K5MinorFreeChoosability_compSetoid_le
-- name    : LeanPool.K5MinorFreeChoosability.compSetoid_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:15:04.965134+00:00
-- url     : https://prove2.me/theorems/ac4b5de6-ad9a-46d8-804f-eec8509bfa1c
-- title:
--   K5 Minor Free Choosability: comp Setoid le
-- statement:
--   The K5 Minor Free Choosability construction uses the comp Setoid le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/LeanPool/K5MinorFreeChoosability/Planar/Hypermap.lean#L54-L64
-- source:
--   https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/LeanPool/K5MinorFreeChoosability/Planar/Hypermap.lean#L54-L64

module
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Planar_Orbits
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Planar_Hypermap
set_option autoImplicit true
@[expose] public section
public section
open LeanPool LeanPool.K5MinorFreeChoosability
open Equiv Equiv.Perm
variable {D : Type*}

theorem LeanPool.K5MinorFreeChoosability.compSetoid_le (r : Setoid D) {σ α : Perm D} (hσ : ∀ z, r z (σ z))
    (hα : ∀ z, r z (α z)) {a b : D} (h : compSetoid σ α a b) : r a b := by sorry
