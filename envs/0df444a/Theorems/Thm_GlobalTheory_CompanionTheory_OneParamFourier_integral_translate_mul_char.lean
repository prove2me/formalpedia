-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_OneParamFourier_integral_translate_mul_char
-- name    : GlobalTheory.CompanionTheory.OneParamFourier.integral_translate_mul_char
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T11:53:13.978907+00:00
-- url     : https://prove2.me/theorems/443accad-128e-46b9-812c-25567316d037
-- title:
--   One Param Fourier: integral translate mul char
-- statement:
--   The One Param Fourier construction uses the integral translate mul char property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FourierOneParameterIntegral.lean#L9-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FourierOneParameterIntegral.lean#L9-L17

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

theorem GlobalTheory.CompanionTheory.OneParamFourier.integral_translate_mul_char (lam : Measure A) [lam.IsAddHaarMeasure] (H : A → ℂ)
    (χ : AddChar A ℂ) (a : A) :
    ∫ b, H (b + a) * χ b ∂lam = χ (-a) * ∫ b, H b * χ b ∂lam := by sorry
