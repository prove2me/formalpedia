-- Prove2me | Theorems.Thm_GlobalTheory_TailIntegralOfSummatory_sum_eq
-- name    : GlobalTheory.TailIntegralOfSummatory.sum_eq
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T22:51:26.354664+00:00
-- url     : https://prove2.me/theorems/cd13136f-653f-471b-ba9e-c451011d3af3
-- title:
--   Tail Integral Of Summatory: sum eq
-- statement:
--   The Tail Integral Of Summatory construction uses the sum eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/KroneckerReal.lean#L16-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/KroneckerReal.lean#L16-L25

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

theorem GlobalTheory.TailIntegralOfSummatory.sum_eq (a : ℕ → ℂ) (N : ℕ) :
    ∑ n ∈ Icc 1 N, a n = N * recSum a N - ∑ k ∈ range N, recSum a k := by sorry
