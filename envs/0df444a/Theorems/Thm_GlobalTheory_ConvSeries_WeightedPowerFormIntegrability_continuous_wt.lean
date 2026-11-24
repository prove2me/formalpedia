-- Prove2me | Theorems.Thm_GlobalTheory_ConvSeries_WeightedPowerFormIntegrability_continuous_wt
-- name    : GlobalTheory.ConvSeries.WeightedPowerFormIntegrability.continuous_wt
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T20:41:57.709843+00:00
-- url     : https://prove2.me/theorems/9f086b23-b01b-49a5-830c-fbb015882b55
-- title:
--   Weighted Power Form Integrability: continuous wt
-- statement:
--   The Weighted Power Form Integrability construction uses the continuous wt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HasSumGaussianConvolutionSeriesTermIntegral.lean#L30-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HasSumGaussianConvolutionSeriesTermIntegral.lean#L30-L33

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

theorem GlobalTheory.ConvSeries.WeightedPowerFormIntegrability.continuous_wt (b c : ℝ) (h : SchwartzMap E ℂ) : Continuous (wt b c h) := by sorry
