-- Prove2me | Theorems.Thm_GlobalTheory_ConvSeries_WeightedPowerFormIntegrability_pow_mul_exp_le
-- name    : GlobalTheory.ConvSeries.WeightedPowerFormIntegrability.pow_mul_exp_le
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T20:41:46.157359+00:00
-- url     : https://prove2.me/theorems/6feb8f5b-8be4-4fd1-9539-029c6ec1933d
-- title:
--   Weighted Power Form Integrability: pow mul exp le
-- statement:
--   The Weighted Power Form Integrability construction uses the pow mul exp le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HasSumGaussianConvolutionSeriesTermIntegral.lean#L62-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HasSumGaussianConvolutionSeriesTermIntegral.lean#L62-L76

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

theorem GlobalTheory.ConvSeries.WeightedPowerFormIntegrability.pow_mul_exp_le {β : ℝ} (hβ : 0 < β) (k : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    x ^ k * Real.exp (-(β * x ^ 2)) ≤
      k.factorial * Real.exp (1 / (2 * β)) * Real.exp (-(β / 2 * x ^ 2)) := by sorry
