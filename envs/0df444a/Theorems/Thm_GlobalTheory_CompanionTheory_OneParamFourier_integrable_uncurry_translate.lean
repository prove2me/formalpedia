-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_OneParamFourier_integrable_uncurry_translate
-- name    : GlobalTheory.CompanionTheory.OneParamFourier.integrable_uncurry_translate
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T11:53:17.344409+00:00
-- url     : https://prove2.me/theorems/4add6239-bc56-44b7-8b0f-5cee0b8201c5
-- title:
--   One Param Fourier: integrable uncurry translate
-- statement:
--   The One Param Fourier construction uses the integrable uncurry translate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FourierOneParameterIntegral.lean#L26-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FourierOneParameterIntegral.lean#L26-L49

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

theorem GlobalTheory.CompanionTheory.OneParamFourier.integrable_uncurry_translate (lam : Measure A) [lam.IsAddHaarMeasure] [SFinite lam]
    (c : ℝ →+ A) (hc : Continuous c) {G : A → ℂ} (hG : Continuous G) (hGi : Integrable G lam)
    {χ : AddChar A ℂ} (hχ : Continuous χ) (hn : ∀ x, ‖χ x‖ = 1) (K : ℂ) (s : ℝ) :
    Integrable (Function.uncurry fun (u : ℝ) (b : A) => K * G (b + c u) * χ b)
      ((volume.restrict (Set.uIoc 0 s)).prod lam) := by sorry
