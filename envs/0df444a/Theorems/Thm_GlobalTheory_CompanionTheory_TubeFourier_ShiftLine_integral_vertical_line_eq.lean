-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_TubeFourier_ShiftLine_integral_vertical_line_eq
-- name    : GlobalTheory.CompanionTheory.TubeFourier.ShiftLine.integral_vertical_line_eq
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T12:16:41.94495+00:00
-- url     : https://prove2.me/theorems/1ae524e5-346f-4b29-9cfd-43ffe41ae9c5
-- title:
--   Shift Line: integral vertical line eq
-- statement:
--   The Shift Line construction uses the integral vertical line eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ContourShiftGaussianDecay.lean#L7-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ContourShiftGaussianDecay.lean#L7-L72

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_StripEntire
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_GaussTubeOfTubeGood
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ContourShiftGaussianDecay
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology PositivityTheory.RgEis GlobalTheory.CompanionTheory.TubeFourier
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TubeFourier GlobalTheory.CompanionTheory.TubeFourier.ShiftLine

theorem GlobalTheory.CompanionTheory.TubeFourier.ShiftLine.integral_vertical_line_eq {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℂ Y] [CompleteSpace Y]
    (f : ℂ → Y) (a b M : ℝ) (hab : a ≤ b)
    (hd : DifferentiableOn ℂ f {z : ℂ | z.re ∈ Set.Icc a b})
    (hb : ∀ z : ℂ, z.re ∈ Set.Icc a b → ‖f z‖ ≤ M * Real.exp (-z.im ^ 2)) :
    ∫ y : ℝ, f ⟨a, y⟩ = ∫ y : ℝ, f ⟨b, y⟩ := by sorry
