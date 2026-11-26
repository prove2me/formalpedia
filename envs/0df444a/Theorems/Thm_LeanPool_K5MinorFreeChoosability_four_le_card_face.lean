-- Prove2me | Theorems.Thm_LeanPool_K5MinorFreeChoosability_four_le_card_face
-- name    : LeanPool.K5MinorFreeChoosability.four_le_card_face
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T02:23:06.047132+00:00
-- url     : https://prove2.me/theorems/60b62834-8a7a-40f8-9ec3-0dbb569fd530
-- title:
--   K5 Minor Free Choosability: four le card face
-- statement:
--   In a bipartite simple graph of minimum degree at least two, every face has length at
--   least four.
--
--   Source: https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/LeanPool/K5MinorFreeChoosability/Planar/Nonplanar.lean#L110-L141
-- source:
--   https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/LeanPool/K5MinorFreeChoosability/Planar/Nonplanar.lean#L110-L141

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

theorem LeanPool.K5MinorFreeChoosability.four_le_card_face [Finite V] (hdeg : ∀ v, 2 ≤ Nat.card {u // G.Adj v u})
    (side : V → Bool) (hside : ∀ u v, G.Adj u v → side u ≠ side v) (d : G.Dart) :
    4 ≤ Nat.card {e // SameCycle (σ * dartSymm G) d e} := by sorry
