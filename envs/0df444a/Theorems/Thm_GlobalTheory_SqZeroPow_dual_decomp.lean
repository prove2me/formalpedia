-- Prove2me | Theorems.Thm_GlobalTheory_SqZeroPow_dual_decomp
-- name    : GlobalTheory.SqZeroPow.dual_decomp
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T20:25:05.805457+00:00
-- url     : https://prove2.me/theorems/5bde0118-907b-4c39-853e-60b7b1adc0a2
-- title:
--   Sq Zero Pow: dual decomp
-- statement:
--   The Sq Zero Pow construction uses the dual decomp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsRingSqZeroNilpotentAugmented.lean#L7-L10
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsRingSqZeroNilpotentAugmented.lean#L7-L10

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

theorem GlobalTheory.SqZeroPow.dual_decomp {R : Type} [CommRing R] (b : DualNumber R) (r s : R) (h : r * s = b.fst) :
    TrivSqZeroExt.inl b.snd * (DualNumber.eps : DualNumber R)
      + TrivSqZeroExt.inl s * TrivSqZeroExt.inl r = b := by sorry
