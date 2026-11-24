-- Prove2me | Theorems.Thm_GlobalTheory_SqZeroPow_dual_inl_pow
-- name    : GlobalTheory.SqZeroPow.dual_inl_pow
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T20:25:19.977493+00:00
-- url     : https://prove2.me/theorems/768ffbd1-0ff1-4acc-b385-da6c20175514
-- title:
--   Sq Zero Pow: dual inl pow
-- statement:
--   The Sq Zero Pow construction uses the dual inl pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsRingSqZeroNilpotentAugmented.lean#L18-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsRingSqZeroNilpotentAugmented.lean#L18-L20

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsRingSqZeroNilpotentAugmented
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory GlobalTheory.SqZeroPow

theorem GlobalTheory.SqZeroPow.dual_inl_pow {R : Type} [CommRing R] (r : R) (n : ℕ) (h : r ^ n = 0) :
    (TrivSqZeroExt.inl r : DualNumber R) ^ n = 0 := by sorry
