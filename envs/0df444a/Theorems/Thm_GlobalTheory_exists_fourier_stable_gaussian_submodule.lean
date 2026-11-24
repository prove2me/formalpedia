-- Prove2me | Theorems.Thm_GlobalTheory_exists_fourier_stable_gaussian_submodule
-- name    : GlobalTheory.exists_fourier_stable_gaussian_submodule
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T22:32:17.061096+00:00
-- url     : https://prove2.me/theorems/60ea24a5-3a8f-4c87-8dde-ecaa3aa2cdf4
-- title:
--   Global Theory: exists fourier stable gaussian submodule
-- statement:
--   The Global Theory construction uses the exists fourier stable gaussian submodule property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsFourierStableGaussianSubmodule.lean#L6-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsFourierStableGaussianSubmodule.lean#L6-L70

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsFourierStableGaussianSubmodule
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open FourierTransform MeasureTheory Filter Topology
open GlobalTheory

theorem GlobalTheory.exists_fourier_stable_gaussian_submodule :
    ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (N : Submodule ℂ (SchwartzMap E ℂ)) (G : SchwartzMap E ℂ),
    (∀ y, G y = Complex.exp (-((Real.pi * ‖y‖ ^ 2 : ℝ) : ℂ))) → G ∈ N →
    (∀ (v : E) (f f₁ : SchwartzMap E ℂ), f ∈ N → (∀ x, f₁ x = fderiv ℝ (⇑f) x v) → f₁ ∈ N) →
    (∀ (ℓ : E →L[ℝ] ℝ) (f f₁ : SchwartzMap E ℂ), f ∈ N → (∀ x, f₁ x = (ℓ x : ℂ) * f x) → f₁ ∈ N) →
    ∃ W : Submodule ℂ (SchwartzMap E ℂ), W ≤ N ∧ G ∈ W ∧
      (∀ (ℓ : E →L[ℝ] ℝ) (f f₁ : SchwartzMap E ℂ), f ∈ W → (∀ x, f₁ x = (ℓ x : ℂ) * f x) → f₁ ∈ W) ∧
      (∀ f ∈ W, 𝓕 f ∈ W) := by sorry
