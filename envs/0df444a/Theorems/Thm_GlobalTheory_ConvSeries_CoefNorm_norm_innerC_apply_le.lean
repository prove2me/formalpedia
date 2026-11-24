-- Prove2me | Theorems.Thm_GlobalTheory_ConvSeries_CoefNorm_norm_innerC_apply_le
-- name    : GlobalTheory.ConvSeries.CoefNorm.norm_innerC_apply_le
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T20:42:04.315637+00:00
-- url     : https://prove2.me/theorems/411bd7da-0323-49fd-aa4d-6fcf1047884e
-- title:
--   Coef Norm: norm inner C apply le
-- statement:
--   The Coef Norm construction uses the norm inner C apply le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NormGaussianConvolutionSeriesCoefficientLeIntegr.lean#L9-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NormGaussianConvolutionSeriesCoefficientLeIntegr.lean#L9-L13

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

theorem GlobalTheory.ConvSeries.CoefNorm.norm_innerC_apply_le {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (a y : E) :
    ‖innerC a y‖ ≤ ‖a‖ * ‖y‖ := by sorry
