-- Prove2me | Theorems.Thm_LeanPool_K5MinorFreeChoosability_numClasses_congr
-- name    : LeanPool.K5MinorFreeChoosability.numClasses_congr
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:10:38.798054+00:00
-- url     : https://prove2.me/theorems/4b5a0af9-caf6-5084-9e9f-4b8bea2cd443
-- title:
--   K5 Minor Free Choosability: num Classes congr
-- statement:
--   The K5 Minor Free Choosability construction uses the num Classes congr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/LeanPool/K5MinorFreeChoosability/Planar/Orbits.lean#L65-L68
-- source:
--   https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/LeanPool/K5MinorFreeChoosability/Planar/Orbits.lean#L65-L68

module
public import Mathlib
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Planar_Orbits
set_option autoImplicit true
@[expose] public section
public section
open LeanPool LeanPool.K5MinorFreeChoosability
open Equiv Equiv.Perm
variable {α : Type*}

theorem LeanPool.K5MinorFreeChoosability.numClasses_congr {s t : Setoid α} (h : ∀ a b, s a b ↔ t a b) :
    numClasses s = numClasses t := by sorry
