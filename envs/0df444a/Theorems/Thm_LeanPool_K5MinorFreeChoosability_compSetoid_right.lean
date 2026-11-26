-- Prove2me | Theorems.Thm_LeanPool_K5MinorFreeChoosability_compSetoid_right
-- name    : LeanPool.K5MinorFreeChoosability.compSetoid_right
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:15:15.204187+00:00
-- url     : https://prove2.me/theorems/c3c1d90c-c6bf-4ed5-b96b-340667abf19f
-- title:
--   K5 Minor Free Choosability: comp Setoid right
-- statement:
--   The K5 Minor Free Choosability construction uses the comp Setoid right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/LeanPool/K5MinorFreeChoosability/Planar/Hypermap.lean#L69-L70
-- source:
--   https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/LeanPool/K5MinorFreeChoosability/Planar/Hypermap.lean#L69-L70

module
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Planar_Orbits
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Planar_Hypermap
set_option autoImplicit true
@[expose] public section
public section
open LeanPool LeanPool.K5MinorFreeChoosability
open Equiv Equiv.Perm
variable {D : Type*}

theorem LeanPool.K5MinorFreeChoosability.compSetoid_right (σ α : Perm D) (z : D) : compSetoid σ α z (α z) := by sorry
