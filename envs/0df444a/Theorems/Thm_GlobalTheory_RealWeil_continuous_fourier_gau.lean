-- Prove2me | Theorems.Thm_GlobalTheory_RealWeil_continuous_fourier_gau
-- name    : GlobalTheory.RealWeil.continuous_fourier_gau
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T19:16:33.219018+00:00
-- url     : https://prove2.me/theorems/65433ea8-0e60-4888-b26d-82f758cfb102
-- title:
--   Real Weil: continuous fourier gau
-- statement:
--   The Real Weil construction uses the continuous fourier gau property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ContinuousFourierGau.lean#L149-L150
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ContinuousFourierGau.lean#L149-L150

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousFourierGau
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex Matrix
open scoped RealInnerProductSpace ContDiff Real FourierTransform
open GlobalTheory GlobalTheory.RealWeil
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V]
  [BorelSpace V] {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B]
variable {om : V → V → ℝ} {ρ : V → B →L[ℂ] B}
variable {J : V ≃ₗᵢ[ℝ] V}

theorem GlobalTheory.RealWeil.continuous_fourier_gau (h : IsHeis om ρ) (f : B) : Continuous (𝓕 fun u => gau u • ρ u f) := by sorry
