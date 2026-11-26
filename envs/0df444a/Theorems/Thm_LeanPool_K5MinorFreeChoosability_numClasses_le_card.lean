-- Prove2me | Theorems.Thm_LeanPool_K5MinorFreeChoosability_numClasses_le_card
-- name    : LeanPool.K5MinorFreeChoosability.numClasses_le_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:10:53.17369+00:00
-- url     : https://prove2.me/theorems/b9d61126-5895-570c-8c1d-d66ae487e5dd
-- title:
--   K5 Minor Free Choosability: num Classes le card
-- statement:
--   The K5 Minor Free Choosability construction uses the num Classes le card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/LeanPool/K5MinorFreeChoosability/Planar/Orbits.lean#L79-L80
-- source:
--   https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/LeanPool/K5MinorFreeChoosability/Planar/Orbits.lean#L79-L80

module
public import Mathlib
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Planar_Orbits
set_option autoImplicit true
@[expose] public section
public section
open LeanPool LeanPool.K5MinorFreeChoosability
open Equiv Equiv.Perm
variable {α : Type*}

theorem LeanPool.K5MinorFreeChoosability.numClasses_le_card [Finite α] (s : Setoid α) : numClasses s ≤ Nat.card α := by sorry
