-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_TubeFourier_phi_eq_of_convex
-- name    : GlobalTheory.CompanionTheory.TubeFourier.phi_eq_of_convex
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T12:16:53.141116+00:00
-- url     : https://prove2.me/theorems/8ab041ba-5a39-4c2d-8da1-b352870a871f
-- title:
--   Tube Fourier: phi eq of convex
-- statement:
--   The Tube Fourier construction uses the phi eq of convex property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/TubeTransformIndependentOfBase.lean#L11-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/TubeTransformIndependentOfBase.lean#L11-L56

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_StripEntire
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_GaussTubeOfTubeGood
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_TubeTransformHorizontalInvarianceStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_TubeTransformVerticalInvarianceStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_TubeTransformIndependentOfBase
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology PositivityTheory.RgEis GlobalTheory.CompanionTheory.TubeFourier
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TubeFourier

theorem GlobalTheory.CompanionTheory.TubeFourier.phi_eq_of_convex : ∀ (X : Type) [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
    (Ω : Set (ℝ × ℝ)) (G : ℂ × ℂ → X), IsOpen Ω → Convex ℝ Ω → GaussTube G Ω →
    ∀ x ∈ Ω, ∀ x' ∈ Ω, ∀ t : ℝ × ℝ, phi G x t = phi G x' t := by sorry
