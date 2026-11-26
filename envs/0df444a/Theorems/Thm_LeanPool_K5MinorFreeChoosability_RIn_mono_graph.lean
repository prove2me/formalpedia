-- Prove2me | Theorems.Thm_LeanPool_K5MinorFreeChoosability_RIn_mono_graph
-- name    : LeanPool.K5MinorFreeChoosability.RIn.mono_graph
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:09:39.454803+00:00
-- url     : https://prove2.me/theorems/58660568-365d-538e-a9f7-9c4583dc6e2f
-- title:
--   RIn: mono graph
-- statement:
--   The RIn construction uses the mono graph property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/LeanPool/K5MinorFreeChoosability/Reach.lean#L77-L77
-- source:
--   https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/LeanPool/K5MinorFreeChoosability/Reach.lean#L77-L77

module
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Basic
public import Mathlib
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Reach
set_option autoImplicit true
@[expose] public section
public section
open LeanPool LeanPool.K5MinorFreeChoosability
variable {W : Type*}
open LeanPool.K5MinorFreeChoosability.RIn
variable {G G' : SimpleGraph W} {s t : Set W} {a b c : W}

theorem LeanPool.K5MinorFreeChoosability.RIn.mono_graph (h : RIn G s a b) (hG : G ≤ G') : RIn G' s a b := by sorry
