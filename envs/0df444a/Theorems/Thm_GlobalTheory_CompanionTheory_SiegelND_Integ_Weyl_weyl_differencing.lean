-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SiegelND_Integ_Weyl_weyl_differencing
-- name    : GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl.weyl_differencing
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T12:15:32.055793+00:00
-- url     : https://prove2.me/theorems/f6ede140-8094-42b1-82c3-f6cd31a69761
-- title:
--   Weyl: weyl differencing
-- statement:
--   The Weyl construction uses the weyl differencing property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ContinuousSeminormDiffSLe.lean#L240-L252
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ContinuousSeminormDiffSLe.lean#L240-L252

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

theorem GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl.weyl_differencing (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    (f : SchwartzMap V ℂ) (K : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : V → ℝ) (T : V →ₗ[ℝ] V), Continuous q →
      (∀ x y, q (x + y) = q x + q y + inner ℝ x (T y)) →
      ENNReal.ofReal (‖∫ x, f x * Complex.exp (2 * Real.pi * Complex.I * ((q x : ℝ) : ℂ))‖ ^ 2) ≤
        ENNReal.ofReal C * ∫⁻ y, ENNReal.ofReal (((1 + ‖y‖) ^ K)⁻¹ * ((1 + ‖T y‖) ^ K)⁻¹) := by sorry
