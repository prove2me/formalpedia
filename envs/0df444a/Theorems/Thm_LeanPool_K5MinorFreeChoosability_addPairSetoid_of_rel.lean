-- Prove2me | Theorems.Thm_LeanPool_K5MinorFreeChoosability_addPairSetoid_of_rel
-- name    : LeanPool.K5MinorFreeChoosability.addPairSetoid_of_rel
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:12:46.854349+00:00
-- url     : https://prove2.me/theorems/576edb84-083a-5905-9bc0-d86ad2eacaa1
-- title:
--   K5 Minor Free Choosability: add Pair Setoid of rel
-- statement:
--   The K5 Minor Free Choosability construction uses the add Pair Setoid of rel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/LeanPool/K5MinorFreeChoosability/Planar/Orbits.lean#L59-L60
-- source:
--   https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/LeanPool/K5MinorFreeChoosability/Planar/Orbits.lean#L59-L60

module
public import Mathlib
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Planar_Orbits
set_option autoImplicit true
@[expose] public section
public section
open LeanPool LeanPool.K5MinorFreeChoosability
open Equiv Equiv.Perm
variable {α : Type*}

theorem LeanPool.K5MinorFreeChoosability.addPairSetoid_of_rel {s : Setoid α} {x y a b : α} (h : s a b) :
    addPairSetoid s x y a b := by sorry
