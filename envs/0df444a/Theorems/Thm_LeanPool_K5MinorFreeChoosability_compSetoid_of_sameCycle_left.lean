-- Prove2me | Theorems.Thm_LeanPool_K5MinorFreeChoosability_compSetoid_of_sameCycle_left
-- name    : LeanPool.K5MinorFreeChoosability.compSetoid_of_sameCycle_left
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:15:36.887058+00:00
-- url     : https://prove2.me/theorems/c0733467-43b0-5aa0-a820-1b513b7b949e
-- title:
--   K5 Minor Free Choosability: comp Setoid of same Cycle left
-- statement:
--   The K5 Minor Free Choosability construction uses the comp Setoid of same Cycle left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/LeanPool/K5MinorFreeChoosability/Planar/Hypermap.lean#L72-L74
-- source:
--   https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/LeanPool/K5MinorFreeChoosability/Planar/Hypermap.lean#L72-L74

module
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Planar_Orbits
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Planar_Hypermap
set_option autoImplicit true
@[expose] public section
public section
open LeanPool LeanPool.K5MinorFreeChoosability
open Equiv Equiv.Perm
variable {D : Type*}

theorem LeanPool.K5MinorFreeChoosability.compSetoid_of_sameCycle_left {σ α : Perm D} {a b : D} (h : SameCycle σ a b) :
    compSetoid σ α a b := by sorry
