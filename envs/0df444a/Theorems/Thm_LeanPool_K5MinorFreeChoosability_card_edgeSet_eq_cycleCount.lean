-- Prove2me | Theorems.Thm_LeanPool_K5MinorFreeChoosability_card_edgeSet_eq_cycleCount
-- name    : LeanPool.K5MinorFreeChoosability.card_edgeSet_eq_cycleCount
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:16:54.929546+00:00
-- url     : https://prove2.me/theorems/61e72e8a-9225-545d-be4f-f19fc748ed35
-- title:
--   K5 Minor Free Choosability: card edge Set eq cycle Count
-- statement:
--   The cycles of the edge involution are the edges.
--
--   Source: https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/LeanPool/K5MinorFreeChoosability/Planar/Embedding.lean#L99-L125
-- source:
--   https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/LeanPool/K5MinorFreeChoosability/Planar/Embedding.lean#L99-L125

module
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Planar_Hypermap
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Planar_Embedding
set_option autoImplicit true
@[expose] public section
public section
open LeanPool LeanPool.K5MinorFreeChoosability
open Equiv Equiv.Perm
variable {V : Type*} (G : SimpleGraph V)

theorem LeanPool.K5MinorFreeChoosability.card_edgeSet_eq_cycleCount : Nat.card G.edgeSet = cycleCount (dartSymm G) := by sorry
