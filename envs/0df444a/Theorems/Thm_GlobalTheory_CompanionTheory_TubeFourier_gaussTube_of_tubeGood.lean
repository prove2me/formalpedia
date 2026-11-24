-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_TubeFourier_gaussTube_of_tubeGood
-- name    : GlobalTheory.CompanionTheory.TubeFourier.gaussTube_of_tubeGood
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T12:16:32.388954+00:00
-- url     : https://prove2.me/theorems/0b002428-3e92-45aa-a164-431f508767f6
-- title:
--   Tube Fourier: gauss Tube of tube Good
-- statement:
--   The Tube Fourier construction uses the gauss Tube of tube Good property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/GaussTubeOfTubeGood.lean#L58-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/GaussTubeOfTubeGood.lean#L58-L71

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

theorem GlobalTheory.CompanionTheory.TubeFourier.gaussTube_of_tubeGood {T : Type} [TopologicalSpace T] {F : ℂ × ℂ → T → X} {Ω : Set (ℝ × ℝ)}
    (h : TubeGood F Ω) (g : T) : GaussTube (gauss (F · g)) Ω := by sorry
