-- Prove2me | Theorems.Thm_GlobalTheory_ConvSeries_CoefNorm_norm_powForm_le
-- name    : GlobalTheory.ConvSeries.CoefNorm.norm_powForm_le
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T20:41:55.070908+00:00
-- url     : https://prove2.me/theorems/83ba2c6c-7f6a-4165-81d3-741c9adb4511
-- title:
--   Coef Norm: norm pow Form le
-- statement:
--   The Coef Norm construction uses the norm pow Form le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NormGaussianConvolutionSeriesCoefficientLeIntegr.lean#L15-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NormGaussianConvolutionSeriesCoefficientLeIntegr.lean#L15-L24

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PowForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormGaussianConvolutionSeriesCoefficientLeIntegr
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.ConvSeries
open GlobalTheory.ConvSeries.CoefNorm

theorem GlobalTheory.ConvSeries.CoefNorm.norm_powForm_le {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (k : ℕ) (a : E) :
    ‖powForm k a‖ ≤ ‖a‖ ^ k := by sorry
