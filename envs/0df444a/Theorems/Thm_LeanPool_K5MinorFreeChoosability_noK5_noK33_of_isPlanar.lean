-- Prove2me | Theorems.Thm_LeanPool_K5MinorFreeChoosability_noK5_noK33_of_isPlanar
-- name    : LeanPool.K5MinorFreeChoosability.noK5_noK33_of_isPlanar
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T02:26:55.047952+00:00
-- url     : https://prove2.me/theorems/3a0dcfc3-d550-5dc6-b564-f0e1ce4b589f
-- title:
--   K5 Minor Free Choosability: no K5 no K33 of is Planar
-- statement:
--   **Wagner's theorem, forward direction**: a finite planar graph has neither a `K_5` nor a
--   `K_{3,3}` minor.
--
--   Source: https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/LeanPool/K5MinorFreeChoosability/Planar/Nonplanar.lean#L209-L212
-- source:
--   https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/LeanPool/K5MinorFreeChoosability/Planar/Nonplanar.lean#L209-L212

module
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Planar_MinorClosed
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Planar_Nonplanar
set_option autoImplicit true
@[expose] public section
public section
open LeanPool LeanPool.K5MinorFreeChoosability
open Equiv Equiv.Perm
variable {V : Type*} {G : SimpleGraph V}

theorem LeanPool.K5MinorFreeChoosability.noK5_noK33_of_isPlanar [Finite V] (hG : IsPlanar G) :
    ¬ IsMinor (⊤ : SimpleGraph (Fin 5)) G ∧ K33MinorFree G := by sorry
