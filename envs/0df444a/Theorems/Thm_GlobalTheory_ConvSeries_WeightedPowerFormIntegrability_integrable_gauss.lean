-- Prove2me | Theorems.Thm_GlobalTheory_ConvSeries_WeightedPowerFormIntegrability_integrable_gauss
-- name    : GlobalTheory.ConvSeries.WeightedPowerFormIntegrability.integrable_gauss
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T20:41:56.234914+00:00
-- url     : https://prove2.me/theorems/d54247fe-b957-408e-85ba-e0342785583c
-- title:
--   Weighted Power Form Integrability: integrable gauss
-- statement:
--   The Weighted Power Form Integrability construction uses the integrable gauss property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HasSumGaussianConvolutionSeriesTermIntegral.lean#L80-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HasSumGaussianConvolutionSeriesTermIntegral.lean#L80-L87

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PowForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasSumGaussianConvolutionSeriesTermIntegral
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.ConvSeries GlobalTheory.ConvSeries.WeightedPowerFormIntegrability
open GlobalTheory.ConvSeries
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem GlobalTheory.ConvSeries.WeightedPowerFormIntegrability.integrable_gauss {β : ℝ} (hβ : 0 < β) :
    Integrable (fun a : E => Real.exp (-(β * ‖a‖ ^ 2))) := by sorry
