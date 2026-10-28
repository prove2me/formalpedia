-- Prove2me | Theorems.Thm_OAI_ElasticityDistribution_scalar_principal_quantitative_gain
-- name    : OAI.ElasticityDistribution.scalar_principal_quantitative_gain
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T10:46:07.027209+00:00
-- url     : https://prove2.me/theorems/ca835dda-e9e4-46ca-afbc-1cd16705188d
-- title:
--   OAI.ElasticityDistribution.scalar_principal_quantitative_gain: intermediate lemma from OpenAI, Global Uniqueness for the Smooth Isotropic Elasticity Inverse Problem
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Elasticity.global_uniqueness`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Global Uniqueness for the Smooth Isotropic Elasticity Inverse Problem*, OpenAI Math Release, September 24, 2026, result family 372, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ElasticityDistribution.scalar_principal_quantitative_gain` of [lean/OAI/MathematicalPhysics/Elasticity/CGO.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/Elasticity/CGO.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ElasticityDistribution`, with `open MeasureTheory TemperedDistribution`, `open scoped SchwartzMap LineDeriv Laplacian BigOperators`, `open ElasticityAugmented ElasticityRegularity`):
--
--   ```lean
--   theorem scalar_principal_quantitative_gain (k : ℤ) {Ω : Set X} {χ η ξ : X → ℂ}
--       (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hcχ : HasCompactSupport χ)
--       (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hcη : HasCompactSupport η)
--       (hξ : ContDiff ℝ (⊤ : ℕ∞) ξ) (hcξ : HasCompactSupport ξ)
--       (h1 : Set.EqOn η 1 (tsupport χ)) (h2 : Set.EqOn ξ 1 (tsupport η))
--       (hsη : tsupport η ⊆ Ω)
--       (A : Fin 3 → Fin 4 → Fin 4 → Coeff) (V : Fin 4 → Fin 4 → Coeff) :
--       ∃ C : ℝ, 0<C ∧ ∀ (z : Fin 3 → ℂ) (U F : Fin 4 → Dist) (f g : HV),
--         (∀ i, LocalEq Ω (Δ (U i)+lowerPart z A V U i) (F i)) →
--         (∀ i, sobolevInjection (k : ℝ) (f i)=smulLeftCLM ℂ ξ (U i)) →
--         (∀ i, sobolevInjection ((k : ℝ)-1) (g i)=smulLeftCLM ℂ η (F i)) →
--         ∃ q : HV, (∀ i, sobolevInjection ((k : ℝ)+1) (q i)=smulLeftCLM ℂ χ (U i)) ∧
--           ‖q‖ ≤ C*(1+∑ d, ‖z d‖)^2*(‖f‖+‖g‖)
--   ```
--
--   **Definitions.** The statement is written with `OAI.ElasticityAugmented.Smooth`, `OAI.ElasticityAugmented.X`, `OAI.ElasticityDistribution.Coeff`, `OAI.ElasticityDistribution.Dist` and `OAI.ElasticityDistribution.X` (definitions bundle `OAIQ6El000` of this split); `OAI.ElasticityRegularity.sobolevInjection` (definitions bundle `OAIQ6El002` of this split); `OAI.ElasticityDistribution.H`, `OAI.ElasticityDistribution.HV` and `OAI.ElasticityDistribution.LocalEq` (definitions bundle `OAIQ6El004` of this split); `OAI.ElasticityDistribution.lowerPart` (definitions bundle `OAIQ6El006` of this split).
--
--   **Used by.** The proof of `OAI.ElasticityDistribution.normalized_quantitative_gain` of this split imports it.
-- source:
--   OpenAI, Global Uniqueness for the Smooth Isotropic Elasticity Inverse Problem, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 372; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Global-Uniqueness-for-the-Smooth-Isotropic-Elasticity-Inverse-Problem-September-24-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/Elasticity/CGO.lean (declaration OAI.ElasticityDistribution.scalar_principal_quantitative_gain)

import Mathlib
import Definitions.Def_OAIQ6El006

section

attribute [-instance] _root_.OAI.ElasticityGeneralSlicing.cylinder_temperate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ElasticityDistribution
open MeasureTheory TemperedDistribution

section
open scoped SchwartzMap LineDeriv Laplacian BigOperators
open ElasticityAugmented ElasticityRegularity

theorem scalar_principal_quantitative_gain (k : ℤ) {Ω : Set X} {χ η ξ : X → ℂ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hcχ : HasCompactSupport χ)
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hcη : HasCompactSupport η)
    (hξ : ContDiff ℝ (⊤ : ℕ∞) ξ) (hcξ : HasCompactSupport ξ)
    (h1 : Set.EqOn η 1 (tsupport χ)) (h2 : Set.EqOn ξ 1 (tsupport η))
    (hsη : tsupport η ⊆ Ω)
    (A : Fin 3 → Fin 4 → Fin 4 → Coeff) (V : Fin 4 → Fin 4 → Coeff) :
    ∃ C : ℝ, 0<C ∧ ∀ (z : Fin 3 → ℂ) (U F : Fin 4 → Dist) (f g : HV),
      (∀ i, LocalEq Ω (Δ (U i)+lowerPart z A V U i) (F i)) →
      (∀ i, sobolevInjection (k : ℝ) (f i)=smulLeftCLM ℂ ξ (U i)) →
      (∀ i, sobolevInjection ((k : ℝ)-1) (g i)=smulLeftCLM ℂ η (F i)) →
      ∃ q : HV, (∀ i, sobolevInjection ((k : ℝ)+1) (q i)=smulLeftCLM ℂ χ (U i)) ∧
        ‖q‖ ≤ C*(1+∑ d, ‖z d‖)^2*(‖f‖+‖g‖) := by
  sorry

end
open scoped SchwartzMap LineDeriv Laplacian BigOperators ENNReal
open ElasticityAugmented ElasticityRegularity
end ElasticityDistribution

end

end OAI
end
