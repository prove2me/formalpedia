-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_OneParamFourier_integrable_mul_char
-- name    : GlobalTheory.CompanionTheory.OneParamFourier.integrable_mul_char
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:28:15.896663+00:00
-- url     : https://prove2.me/theorems/5eff76fc-50b1-4f2e-b454-7b3819c3bc27
-- title:
--   One Param Fourier: integrable mul char
-- statement:
--   The One Param Fourier construction uses the integrable mul char property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FourierOneParameterIntegral.lean#L19-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FourierOneParameterIntegral.lean#L19-L24

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FourierOneParameterIntegral
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.OneParamFourier
variable {A : Type} [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
  [MeasurableSpace A] [BorelSpace A]

theorem GlobalTheory.CompanionTheory.OneParamFourier.integrable_mul_char {lam : Measure A} {H : A → ℂ} (hH : Integrable H lam)
    {χ : AddChar A ℂ} (hχ : Continuous χ) (hn : ∀ x, ‖χ x‖ = 1) :
    Integrable (fun b => H b * χ b) lam := by sorry
