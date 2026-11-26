-- Prove2me | Theorems.Thm_LeanPool_K5MinorFreeChoosability_RIn_mono_set
-- name    : LeanPool.K5MinorFreeChoosability.RIn.mono_set
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:09:29.249794+00:00
-- url     : https://prove2.me/theorems/bc1364c3-f908-5cbb-bcb8-1d3286ec30a2
-- title:
--   RIn: mono set
-- statement:
--   The RIn construction uses the mono set property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/LeanPool/K5MinorFreeChoosability/Reach.lean#L75-L75
-- source:
--   https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/LeanPool/K5MinorFreeChoosability/Reach.lean#L75-L75

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

theorem LeanPool.K5MinorFreeChoosability.RIn.mono_set (h : RIn G s a b) (hs : s ⊆ t) : RIn G t a b := by sorry
