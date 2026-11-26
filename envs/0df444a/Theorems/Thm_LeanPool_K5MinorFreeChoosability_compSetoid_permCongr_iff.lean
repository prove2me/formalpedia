-- Prove2me | Theorems.Thm_LeanPool_K5MinorFreeChoosability_compSetoid_permCongr_iff
-- name    : LeanPool.K5MinorFreeChoosability.compSetoid_permCongr_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:16:24.22818+00:00
-- url     : https://prove2.me/theorems/a73cfa4f-c6c9-571e-b01f-c94df358782e
-- title:
--   K5 Minor Free Choosability: comp Setoid perm Congr iff
-- statement:
--   The K5 Minor Free Choosability construction uses the comp Setoid perm Congr iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/LeanPool/K5MinorFreeChoosability/Planar/Hypermap.lean#L269-L292
-- source:
--   https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/LeanPool/K5MinorFreeChoosability/Planar/Hypermap.lean#L269-L292

module
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Planar_Orbits
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Planar_Hypermap
set_option autoImplicit true
@[expose] public section
public section
open LeanPool LeanPool.K5MinorFreeChoosability
open Equiv Equiv.Perm
variable {D : Type*}

theorem LeanPool.K5MinorFreeChoosability.compSetoid_permCongr_iff {D' : Type*} (e : D ≃ D') (σ α : Perm D) (a b : D) :
    compSetoid σ α a b ↔ compSetoid (e.permCongr σ) (e.permCongr α) (e a) (e b) := by sorry
