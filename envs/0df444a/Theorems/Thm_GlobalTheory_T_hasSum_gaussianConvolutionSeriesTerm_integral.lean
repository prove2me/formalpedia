-- Prove2me | Theorems.Thm_GlobalTheory_T_hasSum_gaussianConvolutionSeriesTerm_integral
-- name    : GlobalTheory.T.hasSum_gaussianConvolutionSeriesTerm_integral
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:32:56.796997+00:00
-- url     : https://prove2.me/theorems/17cb5814-20bc-40c8-aaac-7b3898d004fa
-- title:
--   T: has Sum gaussian Convolution Series Term integral
-- statement:
--   The T construction uses the has Sum gaussian Convolution Series Term integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HasSumGaussianConvolutionSeriesTermIntegralStatement.lean#L7-L11
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HasSumGaussianConvolutionSeriesTermIntegralStatement.lean#L7-L11

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasSumGaussianConvolutionSeriesTermIntegral
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PowForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasSumGaussianConvolutionSeriesTermIntegralStatement
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

theorem GlobalTheory.T.hasSum_gaussianConvolutionSeriesTerm_integral : ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (b c : ℝ), 0 < b → 0 < c → ∀ (h : SchwartzMap E ℂ) (y : E),
    HasSum (fun k => GlobalTheory.ConvSeries.term b c h k y)
      (∫ a, Complex.exp (-((b * ‖a‖ ^ 2 : ℝ) : ℂ)) * h a * Complex.exp (-((c * ‖y - a‖ ^ 2 : ℝ) : ℂ))) := by sorry
