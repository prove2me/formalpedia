-- Prove2me | Theorems.Thm_LeanPool_K5MinorFreeChoosability_compSetoid_left
-- name    : LeanPool.K5MinorFreeChoosability.compSetoid_left
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:15:04.436825+00:00
-- url     : https://prove2.me/theorems/2cdcabdb-d8a1-5eb9-bd43-d0e1f6148e0d
-- title:
--   K5 Minor Free Choosability: comp Setoid left
-- statement:
--   The K5 Minor Free Choosability construction uses the comp Setoid left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/LeanPool/K5MinorFreeChoosability/Planar/Hypermap.lean#L66-L67
-- source:
--   https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/LeanPool/K5MinorFreeChoosability/Planar/Hypermap.lean#L66-L67

module
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Planar_Orbits
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Planar_Hypermap
set_option autoImplicit true
@[expose] public section
public section
open LeanPool LeanPool.K5MinorFreeChoosability
open Equiv Equiv.Perm
variable {D : Type*}

theorem LeanPool.K5MinorFreeChoosability.compSetoid_left (σ α : Perm D) (z : D) : compSetoid σ α z (σ z) := by sorry
