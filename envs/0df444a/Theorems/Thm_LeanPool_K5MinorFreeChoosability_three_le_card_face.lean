-- Prove2me | Theorems.Thm_LeanPool_K5MinorFreeChoosability_three_le_card_face
-- name    : LeanPool.K5MinorFreeChoosability.three_le_card_face
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T02:22:45.541539+00:00
-- url     : https://prove2.me/theorems/418659b1-c043-5488-8bfc-78cd8ff8d41b
-- title:
--   K5 Minor Free Choosability: three le card face
-- statement:
--   In a simple graph of minimum degree at least two, every face has length at least three.
--
--   Source: https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/LeanPool/K5MinorFreeChoosability/Planar/Nonplanar.lean#L91-L106
-- source:
--   https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/LeanPool/K5MinorFreeChoosability/Planar/Nonplanar.lean#L91-L106

module
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Planar_MinorClosed
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Planar_Nonplanar
set_option autoImplicit true
@[expose] public section
public section
open LeanPool LeanPool.K5MinorFreeChoosability
open Equiv Equiv.Perm
variable {V : Type*} {G : SimpleGraph V}
variable {σ : Perm G.Dart} (hσ : IsRotationSystem G σ)
include hσ

theorem LeanPool.K5MinorFreeChoosability.three_le_card_face [Finite V] (hdeg : ∀ v, 2 ≤ Nat.card {u // G.Adj v u})
    (d : G.Dart) : 3 ≤ Nat.card {e // SameCycle (σ * dartSymm G) d e} := by sorry
