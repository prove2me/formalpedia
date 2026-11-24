-- Prove2me | Theorems.Thm_GlobalTheory_ConvSeries_CoefNorm_continuous_wt
-- name    : GlobalTheory.ConvSeries.CoefNorm.continuous_wt
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T20:41:57.520801+00:00
-- url     : https://prove2.me/theorems/4521c108-e912-4be8-88e6-6df12c7ece40
-- title:
--   Coef Norm: continuous wt
-- statement:
--   The Coef Norm construction uses the continuous wt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NormGaussianConvolutionSeriesCoefficientLeIntegr.lean#L36-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NormGaussianConvolutionSeriesCoefficientLeIntegr.lean#L36-L39

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

theorem GlobalTheory.ConvSeries.CoefNorm.continuous_wt {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (b c : ℝ) (h : E → ℂ)
    (hh : Continuous h) : Continuous (wt b c h) := by sorry
