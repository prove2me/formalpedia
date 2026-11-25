-- Prove2me | Theorems.Thm_GlobalTheory_T_archimedean_orbital_integral_continuous
-- name    : GlobalTheory.T.archimedean_orbital_integral_continuous
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:26:58.87635+00:00
-- url     : https://prove2.me/theorems/ea628580-e4af-5084-8f51-07181758ac8f
-- title:
--   T: archimedean orbital integral continuous
-- statement:
--   The T construction uses the archimedean orbital integral continuous property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ArchimedeanOrbitalIntegralContinuousStatement.lean#L8-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ArchimedeanOrbitalIntegralContinuousStatement.lean#L8-L12

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ArchimedeanOrbitalIntegralContinuous
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SecondCountableHermC
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ArchimedeanOrbitalIntegralContinuousStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open GlobalTheory.CompanionTheory.SiegelND.Integ.Arch
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.archimedean_orbital_integral_continuous : ∀ (W : Type) [Fintype W] (n M : ℕ) (J : W → Matrix (Fin M) (Fin M) ℂ)
  (N : ℕ) (e : (W → Fin n → Fin M → ℂ) ≃+ (Fin N → ℝ)), Continuous e → Continuous e.symm →
  ∀ (f : SchwartzMap (Fin N → ℝ) ℂ) (μ : Measure (W → Fin n → Fin M → ℂ)), μ.IsAddHaarMeasure →
  Continuous (coreC J μ (fun X => f (e X))) := by sorry
