-- Prove2me | Theorems.Thm_LeanPool_K5MinorFreeChoosability_restrict_adj
-- name    : LeanPool.K5MinorFreeChoosability.restrict_adj
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:09:31.920323+00:00
-- url     : https://prove2.me/theorems/7bf81218-ac05-52ed-8e7d-6c93c68dda10
-- title:
--   K5 Minor Free Choosability: restrict adj
-- statement:
--   The K5 Minor Free Choosability construction uses the restrict adj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/LeanPool/K5MinorFreeChoosability/Reach.lean#L41-L42
-- source:
--   https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/LeanPool/K5MinorFreeChoosability/Reach.lean#L41-L42

module
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Basic
public import Mathlib
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Reach
set_option autoImplicit true
@[expose] public section
public section
open LeanPool LeanPool.K5MinorFreeChoosability
variable {W : Type*}

theorem LeanPool.K5MinorFreeChoosability.restrict_adj {G : SimpleGraph W} {s : Set W} {a b : W} :
    (restrict G s).Adj a b ↔ G.Adj a b ∧ a ∈ s ∧ b ∈ s := by sorry
