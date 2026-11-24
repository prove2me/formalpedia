-- Prove2me | Theorems.Thm_GlobalTheory_TermEst_main
-- name    : GlobalTheory.TermEst.main
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T21:03:20.144015+00:00
-- url     : https://prove2.me/theorems/a2c92405-069e-47aa-b7c9-93048bac9eb8
-- title:
--   Term Est: main
-- statement:
--   The Term Est construction uses the main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/GaussianConvolutionSeriesCoefficientDescFactoria.lean#L39-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/GaussianConvolutionSeriesCoefficientDescFactoria.lean#L39-L75

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

theorem GlobalTheory.TermEst.main : ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (b c θ α : ℝ), 0 < c → 1 ≤ θ → 0 < α → c * θ ^ 2 ≤ α * (b + c) →
    ∀ (h : SchwartzMap E ℂ) (j i : ℕ) (y : E),
    (2 * c) ^ j / (j.factorial : ℝ) * (j.descFactorial i : ℝ) * (∫ a, ‖GlobalTheory.ConvSeries.wt b c (⇑h) a‖ * ‖a‖ ^ j) *
      ‖y‖ ^ (j - i) ≤ θ⁻¹ ^ (j - i) * Real.exp (c * α * ‖y‖ ^ 2) * ∫ a, (2 * c * ‖a‖) ^ i * ‖h a‖ := by sorry
