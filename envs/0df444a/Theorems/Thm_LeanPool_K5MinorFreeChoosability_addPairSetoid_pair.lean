-- Prove2me | Theorems.Thm_LeanPool_K5MinorFreeChoosability_addPairSetoid_pair
-- name    : LeanPool.K5MinorFreeChoosability.addPairSetoid_pair
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:12:51.803567+00:00
-- url     : https://prove2.me/theorems/689c84ef-7531-5bca-a960-b8724ddfcb9a
-- title:
--   K5 Minor Free Choosability: add Pair Setoid pair
-- statement:
--   The K5 Minor Free Choosability construction uses the add Pair Setoid pair property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/LeanPool/K5MinorFreeChoosability/Planar/Orbits.lean#L62-L63
-- source:
--   https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/LeanPool/K5MinorFreeChoosability/Planar/Orbits.lean#L62-L63

module
public import Mathlib
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Planar_Orbits
set_option autoImplicit true
@[expose] public section
public section
open LeanPool LeanPool.K5MinorFreeChoosability
open Equiv Equiv.Perm
variable {α : Type*}

theorem LeanPool.K5MinorFreeChoosability.addPairSetoid_pair (s : Setoid α) (x y : α) : addPairSetoid s x y x y := by sorry
