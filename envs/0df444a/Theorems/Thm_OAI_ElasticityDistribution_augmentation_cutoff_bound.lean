-- Prove2me | Theorems.Thm_OAI_ElasticityDistribution_augmentation_cutoff_bound
-- name    : OAI.ElasticityDistribution.augmentation_cutoff_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T10:38:44.139831+00:00
-- url     : https://prove2.me/theorems/51655647-c9f7-40f9-ba10-0a95428ebdc5
-- title:
--   OAI.ElasticityDistribution.augmentation_cutoff_bound: intermediate lemma from OpenAI, Global Uniqueness for the Smooth Isotropic Elasticity Inverse Problem
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Elasticity.global_uniqueness`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Global Uniqueness for the Smooth Isotropic Elasticity Inverse Problem*, OpenAI Math Release, September 24, 2026, result family 372, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ElasticityDistribution.augmentation_cutoff_bound` of [lean/OAI/MathematicalPhysics/Elasticity/CGO.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/Elasticity/CGO.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ElasticityDistribution`, with `open MeasureTheory TemperedDistribution`, `open scoped SchwartzMap LineDeriv Laplacian BigOperators ENNReal`, `open ElasticityAugmented ElasticityRegularity`):
--
--   ```lean
--   theorem augmentation_cutoff_bound {η : X → ℂ}
--       (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hcη : HasCompactSupport η) :
--       ∃ C : ℝ, 0<C ∧ ∀ (z : Fin 3 → ℂ) (f : H3),
--         ∃ q : HV, (∀ i, sobolevInjection (-1) (q i)=smulLeftCLM ℂ η
--           ((Fin.cons (divd z (fun j => (f j : Dist))) (fun j => (f j : Dist)) : Fin 4 → Dist) i)) ∧
--           ‖q‖ ≤ C*(1+∑ d, ‖z d‖)^2*‖f‖
--   ```
--
--   **Definitions.** The statement is written with `OAI.ElasticityDistribution.Dist` and `OAI.ElasticityDistribution.X` (definitions bundle `OAIQ6El000` of this split); `OAI.ElasticityRegularity.sobolevInjection` (definitions bundle `OAIQ6El002` of this split); `OAI.ElasticityDistribution.H`, `OAI.ElasticityDistribution.H3`, `OAI.ElasticityDistribution.HV` and `OAI.ElasticityDistribution.divd` (definitions bundle `OAIQ6El004` of this split).
--
--   **Used by.** The proof of `OAI.ElasticityDistribution.physical_quantitative_H1` of this split imports it.
-- source:
--   OpenAI, Global Uniqueness for the Smooth Isotropic Elasticity Inverse Problem, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 372; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Global-Uniqueness-for-the-Smooth-Isotropic-Elasticity-Inverse-Problem-September-24-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/Elasticity/CGO.lean (declaration OAI.ElasticityDistribution.augmentation_cutoff_bound)

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

theorem augmentation_cutoff_bound {η : X → ℂ}
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hcη : HasCompactSupport η) :
    ∃ C : ℝ, 0<C ∧ ∀ (z : Fin 3 → ℂ) (f : H3),
      ∃ q : HV, (∀ i, sobolevInjection (-1) (q i)=smulLeftCLM ℂ η
        ((Fin.cons (divd z (fun j => (f j : Dist))) (fun j => (f j : Dist)) : Fin 4 → Dist) i)) ∧
        ‖q‖ ≤ C*(1+∑ d, ‖z d‖)^2*‖f‖ := by
  sorry

end ElasticityDistribution

end

end OAI
end
