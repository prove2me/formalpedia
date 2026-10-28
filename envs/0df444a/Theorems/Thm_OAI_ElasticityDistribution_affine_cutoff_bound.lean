-- Prove2me | Theorems.Thm_OAI_ElasticityDistribution_affine_cutoff_bound
-- name    : OAI.ElasticityDistribution.affine_cutoff_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T10:38:18.378992+00:00
-- url     : https://prove2.me/theorems/7976cda1-bb23-407d-94b3-4dc0a7f6f587
-- title:
--   OAI.ElasticityDistribution.affine_cutoff_bound: intermediate lemma from OpenAI, Global Uniqueness for the Smooth Isotropic Elasticity Inverse Problem
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Elasticity.global_uniqueness`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Global Uniqueness for the Smooth Isotropic Elasticity Inverse Problem*, OpenAI Math Release, September 24, 2026, result family 372, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ElasticityDistribution.affine_cutoff_bound` of [lean/OAI/MathematicalPhysics/Elasticity/CGO.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/Elasticity/CGO.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ElasticityDistribution`, with `open MeasureTheory TemperedDistribution`, `open scoped SchwartzMap LineDeriv Laplacian BigOperators ENNReal`, `open ElasticityAugmented ElasticityRegularity`):
--
--   ```lean
--   theorem affine_cutoff_bound (s : ℝ) {η : X → ℂ}
--       (T₀ : H3 →L[ℂ] Dist) (T₁ : Fin 3 → H3 →L[ℂ] Dist)
--       (h₀ : ∀ f, MemSobolev s 2 (smulLeftCLM ℂ η (T₀ f)))
--       (h₁ : ∀ d f, MemSobolev s 2 (smulLeftCLM ℂ η (T₁ d f))) :
--       ∃ C : ℝ, 0<C ∧ ∀ (z : Fin 3 → ℂ) (f : H3),
--         ∃ q : ElasticityDistribution.H,
--           sobolevInjection s q=smulLeftCLM ℂ η (T₀ f+∑ d, z d • T₁ d f) ∧
--           ‖q‖ ≤ C*(1+∑ d, ‖z d‖)^2*‖f‖
--   ```
--
--   **Definitions.** The statement is written with `OAI.ElasticityDistribution.Dist` and `OAI.ElasticityDistribution.X` (definitions bundle `OAIQ6El000` of this split); `OAI.ElasticityRegularity.sobolevInjection` (definitions bundle `OAIQ6El002` of this split); `OAI.ElasticityDistribution.H` and `OAI.ElasticityDistribution.H3` (definitions bundle `OAIQ6El004` of this split).
--
--   **Used by.** The proofs of `OAI.ElasticityDistribution.augmentation_cutoff_bound` and `OAI.ElasticityDistribution.normSource_cutoff_bound` of this split import it.
-- source:
--   OpenAI, Global Uniqueness for the Smooth Isotropic Elasticity Inverse Problem, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 372; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Global-Uniqueness-for-the-Smooth-Isotropic-Elasticity-Inverse-Problem-September-24-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/Elasticity/CGO.lean (declaration OAI.ElasticityDistribution.affine_cutoff_bound)

import Mathlib
import Definitions.Def_OAIQ6El004

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

open scoped SchwartzMap LineDeriv Laplacian BigOperators ENNReal
open ElasticityAugmented ElasticityRegularity

theorem affine_cutoff_bound (s : ℝ) {η : X → ℂ}
    (T₀ : H3 →L[ℂ] Dist) (T₁ : Fin 3 → H3 →L[ℂ] Dist)
    (h₀ : ∀ f, MemSobolev s 2 (smulLeftCLM ℂ η (T₀ f)))
    (h₁ : ∀ d f, MemSobolev s 2 (smulLeftCLM ℂ η (T₁ d f))) :
    ∃ C : ℝ, 0<C ∧ ∀ (z : Fin 3 → ℂ) (f : H3),
      ∃ q : ElasticityDistribution.H,
        sobolevInjection s q=smulLeftCLM ℂ η (T₀ f+∑ d, z d • T₁ d f) ∧
        ‖q‖ ≤ C*(1+∑ d, ‖z d‖)^2*‖f‖ := by
  sorry

end ElasticityDistribution

end

end OAI
end
