-- Prove2me | Theorems.Thm_GlobalTheory_T_summable_seminorm_gaussianConvolutionSeriesTerm
-- name    : GlobalTheory.T.summable_seminorm_gaussianConvolutionSeriesTerm
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:40:23.947536+00:00
-- url     : https://prove2.me/theorems/64dac926-a08b-4356-a981-de80131d4d1e
-- title:
--   T: summable seminorm gaussian Convolution Series Term
-- statement:
--   The T construction uses the summable seminorm gaussian Convolution Series Term property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SummableSeminormGaussianConvolutionSeriesTermStatement.lean#L7-L11
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SummableSeminormGaussianConvolutionSeriesTermStatement.lean#L7-L11

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SummableSeminormGaussianConvolutionSeriesTerm
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PowForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SummableSeminormGaussianConvolutionSeriesTermStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.summable_seminorm_gaussianConvolutionSeriesTerm : ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (b c : ℝ), 0 < b → 0 < c → ∀ (h : SchwartzMap E ℂ)
    (t : ℕ → SchwartzMap E ℂ), (∀ j y, t j y = GlobalTheory.ConvSeries.term b c h j y) →
    ∀ (k n : ℕ), Summable (fun j => SchwartzMap.seminorm ℂ k n (t j)) := by sorry
