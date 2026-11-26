-- Prove2me | Theorems.Thm_LeanPool_K5MinorFreeChoosability_RIn_head
-- name    : LeanPool.K5MinorFreeChoosability.RIn.head
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:09:31.121182+00:00
-- url     : https://prove2.me/theorems/f7d21c66-e79b-4155-9e31-9faca464ba58
-- title:
--   RIn: head
-- statement:
--   The RIn construction uses the head property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/LeanPool/K5MinorFreeChoosability/Reach.lean#L62-L63
-- source:
--   https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/LeanPool/K5MinorFreeChoosability/Reach.lean#L62-L63

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

theorem LeanPool.K5MinorFreeChoosability.RIn.head (h : G.Adj a b) (ha : a ∈ s) (hb : b ∈ s) (h₁ : RIn G s b c) : RIn G s a c := by sorry
