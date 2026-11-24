-- Prove2me | Theorems.Thm_GlobalTheory_integral_intervalIntegral_mul_right_curve
-- name    : GlobalTheory.integral_intervalIntegral_mul_right_curve
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T22:56:14.509508+00:00
-- url     : https://prove2.me/theorems/baf93112-b731-4d97-a4db-99cdbbaa170e
-- title:
--   Global Theory: integral interval Integral mul right curve
-- statement:
--   The Global Theory construction uses the integral interval Integral mul right curve property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/RightTranslationCurveSqLeAndIntegralDerivEqZeroA.lean#L8-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/RightTranslationCurveSqLeAndIntegralDerivEqZeroA.lean#L8-L26

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_RightTranslationCurveSqLeAndIntegralDerivEqZeroA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology
open scoped ContDiff
open GlobalTheory

theorem GlobalTheory.integral_intervalIntegral_mul_right_curve {K : Type} [Group K] [TopologicalSpace K]
    [IsTopologicalGroup K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
    (μ : Measure K) [μ.IsMulRightInvariant] [IsProbabilityMeasure μ]
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [SecondCountableTopology E]
    (c : ℝ → K) (hc : Continuous c) (g : K → E) (hg : Continuous g) :
    ∫ x, (∫ t in (0:ℝ)..1, g (x * c t)) ∂μ = ∫ x, g x ∂μ := by sorry
