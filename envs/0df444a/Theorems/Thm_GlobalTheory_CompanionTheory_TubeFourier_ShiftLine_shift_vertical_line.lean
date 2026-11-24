-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_TubeFourier_ShiftLine_shift_vertical_line
-- name    : GlobalTheory.CompanionTheory.TubeFourier.ShiftLine.shift_vertical_line
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T12:16:21.214006+00:00
-- url     : https://prove2.me/theorems/15b023b3-4e9b-4a62-9512-ab66f6049492
-- title:
--   Shift Line: shift vertical line
-- statement:
--   The Shift Line construction uses the shift vertical line property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ContourShiftGaussianDecay.lean#L74-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ContourShiftGaussianDecay.lean#L74-L79

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

theorem GlobalTheory.CompanionTheory.TubeFourier.ShiftLine.shift_vertical_line : ∀ (Y : Type) [NormedAddCommGroup Y] [NormedSpace ℂ Y] [CompleteSpace Y]
    (f : ℂ → Y) (a b M : ℝ), a ≤ b → DifferentiableOn ℂ f {z : ℂ | z.re ∈ Set.Icc a b} →
    (∀ z : ℂ, z.re ∈ Set.Icc a b → ‖f z‖ ≤ M * Real.exp (-z.im ^ 2)) →
    ∫ y : ℝ, f ⟨a, y⟩ = ∫ y : ℝ, f ⟨b, y⟩ := by sorry
