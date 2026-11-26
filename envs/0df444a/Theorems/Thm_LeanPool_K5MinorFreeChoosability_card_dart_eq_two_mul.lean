-- Prove2me | Theorems.Thm_LeanPool_K5MinorFreeChoosability_card_dart_eq_two_mul
-- name    : LeanPool.K5MinorFreeChoosability.card_dart_eq_two_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:17:14.301786+00:00
-- url     : https://prove2.me/theorems/6068cacb-4a0c-43fb-b2c9-8d358ad184cb
-- title:
--   K5 Minor Free Choosability: card dart eq two mul
-- statement:
--   The K5 Minor Free Choosability construction uses the card dart eq two mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/LeanPool/K5MinorFreeChoosability/Planar/Embedding.lean#L127-L131
-- source:
--   https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/LeanPool/K5MinorFreeChoosability/Planar/Embedding.lean#L127-L131

module
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Planar_Hypermap
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Planar_Embedding
set_option autoImplicit true
@[expose] public section
public section
open LeanPool LeanPool.K5MinorFreeChoosability
open Equiv Equiv.Perm
variable {V : Type*} (G : SimpleGraph V)

theorem LeanPool.K5MinorFreeChoosability.card_dart_eq_two_mul [Finite V] : Nat.card G.Dart = 2 * cycleCount (dartSymm G) := by sorry
