-- Prove2me | Theorems.Thm_LeanPool_K5MinorFreeChoosability_RIn_single
-- name    : LeanPool.K5MinorFreeChoosability.RIn.single
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:10:00.357379+00:00
-- url     : https://prove2.me/theorems/131b47e3-3c48-4586-9d34-b1b500b5686e
-- title:
--   RIn: single
-- statement:
--   The RIn construction uses the single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/LeanPool/K5MinorFreeChoosability/Reach.lean#L56-L57
-- source:
--   https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/LeanPool/K5MinorFreeChoosability/Reach.lean#L56-L57

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

theorem LeanPool.K5MinorFreeChoosability.RIn.single (h : G.Adj a b) (ha : a ∈ s) (hb : b ∈ s) : RIn G s a b := by sorry
