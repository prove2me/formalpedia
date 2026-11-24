-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SiegelND_Integ_Weyl_fourier_diffS_decay
-- name    : GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl.fourier_diffS_decay
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T12:13:51.847834+00:00
-- url     : https://prove2.me/theorems/c68eab7f-663c-4c6f-8f57-6bfa5e14447a
-- title:
--   Weyl: fourier diff S decay
-- statement:
--   The Weyl construction uses the fourier diff S decay property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ContinuousSeminormDiffSLe.lean#L137-L168
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ContinuousSeminormDiffSLe.lean#L137-L168

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SecondCountableHermC
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ContinuousSeminormDiffSLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.SiegelND.Integ GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl
open MeasureTheory
open scoped ComplexConjugate FourierTransform
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

theorem GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl.fourier_diffS_decay (f : SchwartzMap V ℂ) (K : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y ξ : V,
      ‖𝓕 (diffS f y) ξ‖ ≤ C * (((1 + ‖y‖) ^ K)⁻¹ * ((1 + ‖ξ‖) ^ K)⁻¹) := by sorry
