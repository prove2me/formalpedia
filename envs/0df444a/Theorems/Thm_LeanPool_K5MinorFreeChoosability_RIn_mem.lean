-- Prove2me | Theorems.Thm_LeanPool_K5MinorFreeChoosability_RIn_mem
-- name    : LeanPool.K5MinorFreeChoosability.RIn.mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:09:56.855745+00:00
-- url     : https://prove2.me/theorems/a5400bb4-09e6-4875-9bb0-c1e4d0635d79
-- title:
--   RIn: mem
-- statement:
--   The RIn construction uses the mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/LeanPool/K5MinorFreeChoosability/Reach.lean#L79-L82
-- source:
--   https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/LeanPool/K5MinorFreeChoosability/Reach.lean#L79-L82

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

theorem LeanPool.K5MinorFreeChoosability.RIn.mem (h : RIn G s a b) (ha : a ∈ s) : b ∈ s := by sorry
