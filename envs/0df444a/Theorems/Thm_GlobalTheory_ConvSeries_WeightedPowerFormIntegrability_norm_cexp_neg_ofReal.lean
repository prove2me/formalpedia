-- Prove2me | Theorems.Thm_GlobalTheory_ConvSeries_WeightedPowerFormIntegrability_norm_cexp_neg_ofReal
-- name    : GlobalTheory.ConvSeries.WeightedPowerFormIntegrability.norm_cexp_neg_ofReal
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T20:41:38.473798+00:00
-- url     : https://prove2.me/theorems/b4cac1b0-988b-465a-8964-1a43d6df9ae0
-- title:
--   Weighted Power Form Integrability: norm cexp neg of Real
-- statement:
--   The Weighted Power Form Integrability construction uses the norm cexp neg of Real property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HasSumGaussianConvolutionSeriesTermIntegral.lean#L13-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HasSumGaussianConvolutionSeriesTermIntegral.lean#L13-L14

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

theorem GlobalTheory.ConvSeries.WeightedPowerFormIntegrability.norm_cexp_neg_ofReal (x : ℝ) : ‖Complex.exp (-((x : ℝ) : ℂ))‖ = Real.exp (-x) := by sorry
