-- Prove2me | Theorems.Thm_GlobalTheory_TailIntegralOfSummatory_sum_Icc_zero
-- name    : GlobalTheory.TailIntegralOfSummatory.sum_Icc_zero
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T22:51:26.894346+00:00
-- url     : https://prove2.me/theorems/3c5bf4f5-83ab-439b-b57e-6cf9d70912a1
-- title:
--   Tail Integral Of Summatory: sum Icc zero
-- statement:
--   The Tail Integral Of Summatory construction uses the sum Icc zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/KroneckerReal.lean#L53-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/KroneckerReal.lean#L53-L59

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_SmoothedRemainderRealIntegralFormula
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_KroneckerReal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Filter Topology MeasureTheory
open Formalism.HermitianLattices.GL2PrimeSums
open GlobalTheory GlobalTheory.TailIntegralOfSummatory

theorem GlobalTheory.TailIntegralOfSummatory.sum_Icc_zero (a : ℕ → ℂ) (N : ℕ) :
    ∑ k ∈ Icc 0 N, (if k = 0 then 0 else a k) = ∑ k ∈ Icc 1 N, a k := by sorry
