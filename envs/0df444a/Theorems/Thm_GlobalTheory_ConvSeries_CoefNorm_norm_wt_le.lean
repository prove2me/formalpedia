-- Prove2me | Theorems.Thm_GlobalTheory_ConvSeries_CoefNorm_norm_wt_le
-- name    : GlobalTheory.ConvSeries.CoefNorm.norm_wt_le
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T20:42:11.384795+00:00
-- url     : https://prove2.me/theorems/67cbd322-def3-4624-a4b9-579d0f61bbdb
-- title:
--   Coef Norm: norm wt le
-- statement:
--   The Coef Norm construction uses the norm wt le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NormGaussianConvolutionSeriesCoefficientLeIntegr.lean#L26-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NormGaussianConvolutionSeriesCoefficientLeIntegr.lean#L26-L34

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

theorem GlobalTheory.ConvSeries.CoefNorm.norm_wt_le {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (b c : ℝ) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (h : E → ℂ) (a : E) : ‖wt b c h a‖ ≤ ‖h a‖ := by sorry
