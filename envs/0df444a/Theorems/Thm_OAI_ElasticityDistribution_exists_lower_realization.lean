-- Prove2me | Theorems.Thm_OAI_ElasticityDistribution_exists_lower_realization
-- name    : OAI.ElasticityDistribution.exists_lower_realization
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T10:45:34.061998+00:00
-- url     : https://prove2.me/theorems/ca17bfc0-94e6-497a-8ebc-0e6eb673f9df
-- title:
--   OAI.ElasticityDistribution.exists_lower_realization: intermediate lemma from OpenAI, Global Uniqueness for the Smooth Isotropic Elasticity Inverse Problem
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Elasticity.global_uniqueness`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Global Uniqueness for the Smooth Isotropic Elasticity Inverse Problem*, OpenAI Math Release, September 24, 2026, result family 372, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ElasticityDistribution.exists_lower_realization` of [lean/OAI/MathematicalPhysics/Elasticity/CGO.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/Elasticity/CGO.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ElasticityDistribution`, with `open MeasureTheory TemperedDistribution`, `open scoped SchwartzMap LineDeriv Laplacian BigOperators`, `open ElasticityAugmented ElasticityRegularity`):
--
--   ```lean
--   theorem exists_lower_realization (k : ℤ) {η ξ : X → ℂ}
--       (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hcη : HasCompactSupport η)
--       (hξ : ContDiff ℝ (⊤ : ℕ∞) ξ) (hcξ : HasCompactSupport ξ)
--       (h1 : Set.EqOn ξ 1 (tsupport η))
--       (A : Fin 3 → Fin 4 → Fin 4 → Coeff) (V : Fin 4 → Fin 4 → Coeff) (i : Fin 4) :
--       ∃ L₀ L₂ : HV →L[ℂ] H, ∃ L₁ : Fin 3 → HV →L[ℂ] H,
--         ∀ (z : Fin 3 → ℂ) (U : Fin 4 → Dist) (f : HV),
--           (∀ j, sobolevInjection (k : ℝ) (f j)=smulLeftCLM ℂ ξ (U j)) →
--           sobolevInjection ((k : ℝ)-1)
--             ((L₀+(∑ d, z d • L₁ d)+(∑ d, z d*z d) • L₂) f)=
--               smulLeftCLM ℂ η (lowerPart z A V U i)
--   ```
--
--   **Definitions.** The statement is written with `OAI.ElasticityAugmented.Smooth`, `OAI.ElasticityAugmented.X`, `OAI.ElasticityDistribution.Coeff`, `OAI.ElasticityDistribution.Dist` and `OAI.ElasticityDistribution.X` (definitions bundle `OAIQ6El000` of this split); `OAI.ElasticityRegularity.sobolevInjection` (definitions bundle `OAIQ6El002` of this split); `OAI.ElasticityDistribution.H` and `OAI.ElasticityDistribution.HV` (definitions bundle `OAIQ6El004` of this split); `OAI.ElasticityDistribution.lowerPart` (definitions bundle `OAIQ6El006` of this split).
--
--   **Used by.** The proof of `OAI.ElasticityDistribution.lower_realization_bound` of this split imports it.
-- source:
--   OpenAI, Global Uniqueness for the Smooth Isotropic Elasticity Inverse Problem, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 372; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Global-Uniqueness-for-the-Smooth-Isotropic-Elasticity-Inverse-Problem-September-24-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/Elasticity/CGO.lean (declaration OAI.ElasticityDistribution.exists_lower_realization)

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

theorem exists_lower_realization (k : ℤ) {η ξ : X → ℂ}
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hcη : HasCompactSupport η)
    (hξ : ContDiff ℝ (⊤ : ℕ∞) ξ) (hcξ : HasCompactSupport ξ)
    (h1 : Set.EqOn ξ 1 (tsupport η))
    (A : Fin 3 → Fin 4 → Fin 4 → Coeff) (V : Fin 4 → Fin 4 → Coeff) (i : Fin 4) :
    ∃ L₀ L₂ : HV →L[ℂ] H, ∃ L₁ : Fin 3 → HV →L[ℂ] H,
      ∀ (z : Fin 3 → ℂ) (U : Fin 4 → Dist) (f : HV),
        (∀ j, sobolevInjection (k : ℝ) (f j)=smulLeftCLM ℂ ξ (U j)) →
        sobolevInjection ((k : ℝ)-1)
          ((L₀+(∑ d, z d • L₁ d)+(∑ d, z d*z d) • L₂) f)=
            smulLeftCLM ℂ η (lowerPart z A V U i) := by
  sorry

end
open scoped SchwartzMap LineDeriv Laplacian BigOperators ENNReal
open ElasticityAugmented ElasticityRegularity
end ElasticityDistribution

end

end OAI
end
