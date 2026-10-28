-- Prove2me | Theorems.Thm_OAI_ElasticityCoordinates_planar_smooth_representative
-- name    : OAI.ElasticityCoordinates.planar_smooth_representative
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T10:18:18.903415+00:00
-- url     : https://prove2.me/theorems/752514da-f872-4c0c-a75e-848587d4e171
-- title:
--   OAI.ElasticityCoordinates.planar_smooth_representative: intermediate lemma from OpenAI, Global Uniqueness for the Smooth Isotropic Elasticity Inverse Problem
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Elasticity.global_uniqueness`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Global Uniqueness for the Smooth Isotropic Elasticity Inverse Problem*, OpenAI Math Release, September 24, 2026, result family 372, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ElasticityCoordinates.planar_smooth_representative` of [lean/OAI/MathematicalPhysics/Elasticity/Smoothing.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/Elasticity/Smoothing.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ElasticityCoordinates`, with `open Set MeasureTheory TemperedDistribution`, `open scoped SchwartzMap ENNReal LineDeriv`):
--
--   ```lean
--   theorem planar_smooth_representative (L : (P × ℂ) ≃L[ℝ] E)
--       (T K : Set E) (hT : IsCompact T) (hK : IsCompact K)
--       (a : n → n → E → ℂ) (ha : ∀ i j,ContDiff ℝ (⊤ : ℕ∞) (a i j))
--       (has : ∀ i j x,x∉K → a i j x=0)
--       (f : n → E → ℂ) (hf : ∀ i,ContDiff ℝ (⊤ : ℕ∞) (f i))
--       (hfs : ∀ i x,x∉K → f i x=0)
--       (u w : n → Lp ℂ 2 (volume : Measure E))
--       (hus : ∀ i,∀ᵐ x,x∉T → u i x=0) (hws : ∀ i,∀ᵐ x,x∉T → w i x=0)
--       (hc : ∀ i,∀ᵐ x,w i x=∑ j,a i j x*u j x-f i x)
--       (he : ∀ i,∂_{L (0,1)} (u i : 𝓢'(E,ℂ))+
--         Complex.I • ∂_{L (0,Complex.I)} (u i : 𝓢'(E,ℂ))+(w i : 𝓢'(E,ℂ))=0) :
--       ∃ v : n → E → ℂ,(∀ i,ContDiff ℝ (⊤ : ℕ∞) (v i)) ∧
--         (∀ i,(u i : E → ℂ)=ᵐ[volume] v i)
--   ```
--
--   **Used by.** The proof of `OAI.ElasticityDistribution.compact_transport_smoothing` of this split imports it.
-- source:
--   OpenAI, Global Uniqueness for the Smooth Isotropic Elasticity Inverse Problem, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 372; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Global-Uniqueness-for-the-Smooth-Isotropic-Elasticity-Inverse-Problem-September-24-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/Elasticity/Smoothing.lean (declaration OAI.ElasticityCoordinates.planar_smooth_representative)

import Mathlib

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ElasticityCoordinates
open Set MeasureTheory TemperedDistribution
open scoped SchwartzMap ENNReal LineDeriv
variable {E P n : Type*} [Fintype n]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasureSpace E] [BorelSpace E] [Measure.IsAddHaarMeasure (volume : Measure E)]
  [NormedAddCommGroup P] [InnerProductSpace ℝ P] [FiniteDimensional ℝ P]
  [MeasureSpace P] [BorelSpace P] [Measure.IsAddHaarMeasure (volume : Measure P)]

theorem planar_smooth_representative (L : (P × ℂ) ≃L[ℝ] E)
    (T K : Set E) (hT : IsCompact T) (hK : IsCompact K)
    (a : n → n → E → ℂ) (ha : ∀ i j,ContDiff ℝ (⊤ : ℕ∞) (a i j))
    (has : ∀ i j x,x∉K → a i j x=0)
    (f : n → E → ℂ) (hf : ∀ i,ContDiff ℝ (⊤ : ℕ∞) (f i))
    (hfs : ∀ i x,x∉K → f i x=0)
    (u w : n → Lp ℂ 2 (volume : Measure E))
    (hus : ∀ i,∀ᵐ x,x∉T → u i x=0) (hws : ∀ i,∀ᵐ x,x∉T → w i x=0)
    (hc : ∀ i,∀ᵐ x,w i x=∑ j,a i j x*u j x-f i x)
    (he : ∀ i,∂_{L (0,1)} (u i : 𝓢'(E,ℂ))+
      Complex.I • ∂_{L (0,Complex.I)} (u i : 𝓢'(E,ℂ))+(w i : 𝓢'(E,ℂ))=0) :
    ∃ v : n → E → ℂ,(∀ i,ContDiff ℝ (⊤ : ℕ∞) (v i)) ∧
      (∀ i,(u i : E → ℂ)=ᵐ[volume] v i) := by
  sorry

end ElasticityCoordinates
open Set Filter TemperedDistribution
open scoped SchwartzMap LineDeriv BigOperators Topology

end

end OAI
end
