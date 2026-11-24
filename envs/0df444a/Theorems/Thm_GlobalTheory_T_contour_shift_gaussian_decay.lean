-- Prove2me | Theorems.Thm_GlobalTheory_T_contour_shift_gaussian_decay
-- name    : GlobalTheory.T.contour_shift_gaussian_decay
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:35:44.258707+00:00
-- url     : https://prove2.me/theorems/c7f279a4-f25b-4cc6-b838-992949128efe
-- title:
--   T: contour shift gaussian decay
-- statement:
--   The T construction uses the contour shift gaussian decay property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ContourShiftGaussianDecayStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ContourShiftGaussianDecayStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ContourShiftGaussianDecay
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_StripEntire
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_GaussTubeOfTubeGood
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ContourShiftGaussianDecayStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology PositivityTheory.RgEis GlobalTheory.CompanionTheory.TubeFourier
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.contour_shift_gaussian_decay : ∀ (Y : Type) [NormedAddCommGroup Y] [NormedSpace ℂ Y] [CompleteSpace Y] (f : ℂ → Y) (a b M : ℝ), a ≤ b → DifferentiableOn ℂ f {z : ℂ | z.re ∈ Set.Icc a b} → (∀ z : ℂ, z.re ∈ Set.Icc a b → ‖f z‖ ≤ M * Real.exp (-z.im ^ 2)) → ∫ y : ℝ, f ⟨a, y⟩ = ∫ y : ℝ, f ⟨b, y⟩ := by sorry
