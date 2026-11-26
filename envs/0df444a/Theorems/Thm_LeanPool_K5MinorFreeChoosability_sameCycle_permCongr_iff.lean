-- Prove2me | Theorems.Thm_LeanPool_K5MinorFreeChoosability_sameCycle_permCongr_iff
-- name    : LeanPool.K5MinorFreeChoosability.sameCycle_permCongr_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:16:07.609777+00:00
-- url     : https://prove2.me/theorems/d74e73b8-e40b-42c2-94ca-351cc46fbf99
-- title:
--   K5 Minor Free Choosability: same Cycle perm Congr iff
-- statement:
--   The K5 Minor Free Choosability construction uses the same Cycle perm Congr iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/LeanPool/K5MinorFreeChoosability/Planar/Hypermap.lean#L243-L263
-- source:
--   https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/LeanPool/K5MinorFreeChoosability/Planar/Hypermap.lean#L243-L263

module
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Planar_Orbits
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Planar_Hypermap
set_option autoImplicit true
@[expose] public section
public section
open LeanPool LeanPool.K5MinorFreeChoosability
open Equiv Equiv.Perm
variable {D : Type*}

theorem LeanPool.K5MinorFreeChoosability.sameCycle_permCongr_iff {D' : Type*} (e : D ≃ D') (π : Perm D) (a b : D) :
    SameCycle π a b ↔ SameCycle (e.permCongr π) (e a) (e b) := by sorry
