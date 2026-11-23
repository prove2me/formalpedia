-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_TubeFourier_gauss_bound
-- name    : GlobalTheory.CompanionTheory.TubeFourier.gauss_bound
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T19:33:50.987934+00:00
-- url     : https://prove2.me/theorems/27102d64-76e1-4972-9415-feea45c53383
-- title:
--   Tube Fourier: gauss bound
-- statement:
--   The Tube Fourier construction uses the gauss bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/GaussTubeOfTubeGood.lean#L43-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/GaussTubeOfTubeGood.lean#L43-L56

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_StripEntire
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_GaussTubeOfTubeGood
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology PositivityTheory.RgEis
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TubeFourier
variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X]

theorem GlobalTheory.CompanionTheory.TubeFourier.gauss_bound {T : Type} [TopologicalSpace T] {F : ℂ × ℂ → T → X} {Ω C : Set (ℝ × ℝ)} (h : TubeGood F Ω)
    (hC : C ⊆ Ω) (hc : IsCompact C) (g : T) : ∃ U ∈ 𝓝 g, ∃ M : ℝ, ∀ g' ∈ U, ∀ l ∈ tube C,
      ‖gauss (F · g') l‖ ≤ M * Real.exp (-(l.1.im ^ 2 + l.2.im ^ 2)) := by sorry
