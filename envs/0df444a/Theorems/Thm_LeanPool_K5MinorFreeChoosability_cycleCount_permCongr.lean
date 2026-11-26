-- Prove2me | Theorems.Thm_LeanPool_K5MinorFreeChoosability_cycleCount_permCongr
-- name    : LeanPool.K5MinorFreeChoosability.cycleCount_permCongr
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:16:21.287279+00:00
-- url     : https://prove2.me/theorems/99e396d8-122b-5be5-9596-f9332f07b0fb
-- title:
--   K5 Minor Free Choosability: cycle Count perm Congr
-- statement:
--   The K5 Minor Free Choosability construction uses the cycle Count perm Congr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/LeanPool/K5MinorFreeChoosability/Planar/Hypermap.lean#L265-L267
-- source:
--   https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/LeanPool/K5MinorFreeChoosability/Planar/Hypermap.lean#L265-L267

module
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Planar_Orbits
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Planar_Hypermap
set_option autoImplicit true
@[expose] public section
public section
open LeanPool LeanPool.K5MinorFreeChoosability
open Equiv Equiv.Perm
variable {D : Type*}

theorem LeanPool.K5MinorFreeChoosability.cycleCount_permCongr {D' : Type*} (e : D ≃ D') (π : Perm D) :
    cycleCount (e.permCongr π) = cycleCount π := by sorry
