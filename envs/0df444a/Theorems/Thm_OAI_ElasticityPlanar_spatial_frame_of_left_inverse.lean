-- Prove2me | Theorems.Thm_OAI_ElasticityPlanar_spatial_frame_of_left_inverse
-- name    : OAI.ElasticityPlanar.spatial_frame_of_left_inverse
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T10:18:45.516981+00:00
-- url     : https://prove2.me/theorems/3a10e31e-05d3-49e6-b192-29264b58429b
-- title:
--   OAI.ElasticityPlanar.spatial_frame_of_left_inverse: intermediate lemma from OpenAI, Global Uniqueness for the Smooth Isotropic Elasticity Inverse Problem
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Elasticity.global_uniqueness`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Global Uniqueness for the Smooth Isotropic Elasticity Inverse Problem*, OpenAI Math Release, September 24, 2026, result family 372, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ElasticityPlanar.spatial_frame_of_left_inverse` of [lean/OAI/MathematicalPhysics/Elasticity/Transport.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/Elasticity/Transport.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ElasticityPlanar`, with `open Set Complex Module`):
--
--   ```lean
--   theorem spatial_frame_of_left_inverse (J : ℂ →L[ℝ] E) (K : E →L[ℝ] ℂ)
--       (hK : Function.LeftInverse K J)
--       {S Ω Ω' : Set ℂ} (hS : IsCompact S) (hΩS : Ω ⊆ S)
--       (hΩ' : IsOpen Ω') (hsub : Ω' ⊆ Ω) (q : Basis n ℂ R)
--       (A : E → R) (hA : ContDiff ℝ (⊤ : ℕ∞) A)
--       {g : ℂ → ℂ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hc : HasCompactSupport g)
--       (hs : tsupport g ⊆ Ω) (h1 : Set.EqOn g 1 Ω') :
--       ∃ V : E → R, ContDiff ℝ (⊤ : ℕ∞) V ∧ (∀ x, IsUnit (V x)) ∧
--           ∀ x, K x∈Ω' → fderiv ℝ V x (J 1)+I • fderiv ℝ V x (J I)=A x*V x
--   ```
--
--   **Used by.** The proof of `OAI.ElasticityFrame.exists_constraint_columns` of this split imports it.
-- source:
--   OpenAI, Global Uniqueness for the Smooth Isotropic Elasticity Inverse Problem, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 372; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Global-Uniqueness-for-the-Smooth-Isotropic-Elasticity-Inverse-Problem-September-24-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/Elasticity/Transport.lean (declaration OAI.ElasticityPlanar.spatial_frame_of_left_inverse)

import Mathlib

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ElasticityPlanar
open Set Complex Module
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

section
variable {R : Type*} [NormedRing R] [NormedAlgebra ℂ R] [CompleteSpace R] [FiniteDimensional ℂ R]
variable {n : Type*} [Fintype n]

theorem spatial_frame_of_left_inverse (J : ℂ →L[ℝ] E) (K : E →L[ℝ] ℂ)
    (hK : Function.LeftInverse K J)
    {S Ω Ω' : Set ℂ} (hS : IsCompact S) (hΩS : Ω ⊆ S)
    (hΩ' : IsOpen Ω') (hsub : Ω' ⊆ Ω) (q : Basis n ℂ R)
    (A : E → R) (hA : ContDiff ℝ (⊤ : ℕ∞) A)
    {g : ℂ → ℂ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hc : HasCompactSupport g)
    (hs : tsupport g ⊆ Ω) (h1 : Set.EqOn g 1 Ω') :
    ∃ V : E → R, ContDiff ℝ (⊤ : ℕ∞) V ∧ (∀ x, IsUnit (V x)) ∧
        ∀ x, K x∈Ω' → fderiv ℝ V x (J 1)+I • fderiv ℝ V x (J I)=A x*V x := by
  sorry
end

end ElasticityPlanar

end

end OAI
end
