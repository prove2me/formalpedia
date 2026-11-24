-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_TubeFourier_InvLine_inv_differentiable_line
-- name    : GlobalTheory.CompanionTheory.TubeFourier.InvLine.inv_differentiable_line
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T12:16:11.166821+00:00
-- url     : https://prove2.me/theorems/090776fc-0fcb-42fd-ab96-09edfbb7dc2f
-- title:
--   Inv Line: inv differentiable line
-- statement:
--   The Inv Line construction uses the inv differentiable line property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/InverseTransformHolomorphicLines.lean#L42-L136
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/InverseTransformHolomorphicLines.lean#L42-L136

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_StripEntire
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_GaussTubeOfTubeGood
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExponentialFourierIntegralBound
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_InverseTransformHolomorphicLines
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology PositivityTheory.RgEis GlobalTheory.CompanionTheory.TubeFourier
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TubeFourier GlobalTheory.CompanionTheory.TubeFourier.InvLine

theorem GlobalTheory.CompanionTheory.TubeFourier.InvLine.inv_differentiable_line : ∀ (X : Type) [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X] (T : Type) [TopologicalSpace T] (φ : ℝ × ℝ → T → X), ExpDecay φ → (∀ g : T, Continuous fun t => φ t g) → ∀ (g : T) (p v : ℂ × ℂ), Differentiable ℂ (fun τ : ℂ => inv (fun t => φ t g) (p + τ • v)) := by sorry
