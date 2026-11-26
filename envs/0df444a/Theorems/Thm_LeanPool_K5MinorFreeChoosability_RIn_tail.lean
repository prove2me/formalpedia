-- Prove2me | Theorems.Thm_LeanPool_K5MinorFreeChoosability_RIn_tail
-- name    : LeanPool.K5MinorFreeChoosability.RIn.tail
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:09:30.348989+00:00
-- url     : https://prove2.me/theorems/59a84f55-185c-4c77-a601-dee4b2950641
-- title:
--   RIn: tail
-- statement:
--   The RIn construction uses the tail property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/LeanPool/K5MinorFreeChoosability/Reach.lean#L59-L60
-- source:
--   https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/LeanPool/K5MinorFreeChoosability/Reach.lean#L59-L60

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

theorem LeanPool.K5MinorFreeChoosability.RIn.tail (h₁ : RIn G s a b) (h : G.Adj b c) (hb : b ∈ s) (hc : c ∈ s) : RIn G s a c := by sorry
