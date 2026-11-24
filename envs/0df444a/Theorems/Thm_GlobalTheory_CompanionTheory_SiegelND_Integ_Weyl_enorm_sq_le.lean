-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SiegelND_Integ_Weyl_enorm_sq_le
-- name    : GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl.enorm_sq_le
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T12:15:00.029917+00:00
-- url     : https://prove2.me/theorems/2c4ccbe5-0f06-45a4-888b-208a8b8a57cd
-- title:
--   Weyl: enorm sq le
-- statement:
--   The Weyl construction uses the enorm sq le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ContinuousSeminormDiffSLe.lean#L194-L238
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ContinuousSeminormDiffSLe.lean#L194-L238

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

theorem GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl.enorm_sq_le (f : SchwartzMap V ℂ) (q : V → ℝ) (T : V →ₗ[ℝ] V) (hq : Continuous q)
    (hT : ∀ x y, q (x + y) = q x + q y + inner ℝ x (T y)) :
    ENNReal.ofReal (‖∫ x, f x * ee (q x)‖ ^ 2) ≤ ∫⁻ y, ‖𝓕 (diffS f y) (-(T y))‖ₑ := by sorry
