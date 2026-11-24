-- Prove2me | Theorems.Thm_GlobalTheory_T_norm_gaussianConvolutionSeriesCoefficient_le_integral
-- name    : GlobalTheory.T.norm_gaussianConvolutionSeriesCoefficient_le_integral
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T20:55:53.943947+00:00
-- url     : https://prove2.me/theorems/b4aa782f-c5c8-454b-9e06-cbedd34278c7
-- title:
--   T: norm gaussian Convolution Series Coefficient le integral
-- statement:
--   The T construction uses the norm gaussian Convolution Series Coefficient le integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NormGaussianConvolutionSeriesCoefficientLeIntegrStatement.lean#L7-L10
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NormGaussianConvolutionSeriesCoefficientLeIntegrStatement.lean#L7-L10

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormGaussianConvolutionSeriesCoefficientLeIntegr
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PowForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormGaussianConvolutionSeriesCoefficientLeIntegrStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.norm_gaussianConvolutionSeriesCoefficient_le_integral : ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (b c : ℝ), 0 ≤ b → 0 ≤ c → ∀ (h : SchwartzMap E ℂ) (j : ℕ),
    ‖GlobalTheory.ConvSeries.coef b c (⇑h) j‖ ≤ ∫ a, ‖GlobalTheory.ConvSeries.wt b c (⇑h) a‖ * ‖a‖ ^ j := by sorry
