-- Prove2me | Theorems.Thm_GlobalTheory_ConvSeries_WeightedPowerFormIntegrability_coef_apply_const
-- name    : GlobalTheory.ConvSeries.WeightedPowerFormIntegrability.coef_apply_const
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T20:41:53.843514+00:00
-- url     : https://prove2.me/theorems/4cc8f391-4e92-4d53-afda-54c6a70e9376
-- title:
--   Weighted Power Form Integrability: coef apply const
-- statement:
--   The Weighted Power Form Integrability construction uses the coef apply const property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HasSumGaussianConvolutionSeriesTermIntegral.lean#L113-L122
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HasSumGaussianConvolutionSeriesTermIntegral.lean#L113-L122

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

theorem GlobalTheory.ConvSeries.WeightedPowerFormIntegrability.coef_apply_const {b c : ℝ} (hb : 0 < b) (hc : 0 < c) (h : SchwartzMap E ℂ) (k : ℕ) (y : E) :
    coef b c h k (fun _ => y) = ∫ a, wt b c h a * ((inner ℝ a y : ℝ) : ℂ) ^ k := by sorry
