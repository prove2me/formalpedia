-- Prove2me | Theorems.Thm_GlobalTheory_TermEst_norm_wt
-- name    : GlobalTheory.TermEst.norm_wt
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T21:03:24.872802+00:00
-- url     : https://prove2.me/theorems/a1d41e6f-faf4-4db6-b8b2-c18639c89901
-- title:
--   Term Est: norm wt
-- statement:
--   The Term Est construction uses the norm wt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/GaussianConvolutionSeriesCoefficientDescFactoria.lean#L32-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/GaussianConvolutionSeriesCoefficientDescFactoria.lean#L32-L37

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PowForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GaussianConvolutionSeriesCoefficientDescFactoria
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.TermEst

theorem GlobalTheory.TermEst.norm_wt {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (b c : ℝ) (h : E → ℂ) (a : E) :
    ‖GlobalTheory.ConvSeries.wt b c h a‖ = Real.exp (-((b + c) * ‖a‖ ^ 2)) * ‖h a‖ := by sorry
