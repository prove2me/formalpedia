-- Prove2me | Theorems.Thm_LeanPool_K5MinorFreeChoosability_RIn_symm
-- name    : LeanPool.K5MinorFreeChoosability.RIn.symm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:09:32.966224+00:00
-- url     : https://prove2.me/theorems/a70f499d-40a3-487b-9347-56e04b2ed773
-- title:
--   RIn: symm
-- statement:
--   The RIn construction uses the symm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/LeanPool/K5MinorFreeChoosability/Reach.lean#L65-L68
-- source:
--   https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/LeanPool/K5MinorFreeChoosability/Reach.lean#L65-L68

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

theorem LeanPool.K5MinorFreeChoosability.RIn.symm (h : RIn G s a b) : RIn G s b a := by sorry
