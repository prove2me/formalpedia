-- Prove2me | Theorems.Thm_OAI_ElasticityPlanar_supported_weak_unique
-- name    : OAI.ElasticityPlanar.supported_weak_unique
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T10:41:47.372592+00:00
-- url     : https://prove2.me/theorems/2f121383-a2ef-45ba-b37e-e4631e11c51b
-- title:
--   OAI.ElasticityPlanar.supported_weak_unique: intermediate lemma from OpenAI, Global Uniqueness for the Smooth Isotropic Elasticity Inverse Problem
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Elasticity.global_uniqueness`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Global Uniqueness for the Smooth Isotropic Elasticity Inverse Problem*, OpenAI Math Release, September 24, 2026, result family 372, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ElasticityPlanar.supported_weak_unique` of [lean/OAI/MathematicalPhysics/Elasticity/Supported.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/Elasticity/Supported.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ElasticityPlanar`, with `open Set MeasureTheory TemperedDistribution`, `open scoped SchwartzMap ENNReal BigOperators`, `open ElasticityRegularity`):
--
--   ```lean
--   lemma supported_weak_unique {S : Set ℂ} (hS : IsCompact S)
--       (a : n → n → ℂ → ℂ) (ha : ∀ i j, (a i j).HasTemperateGrowth)
--       (u v : Hilbert n) (he : ∀ i, planarOperator a i u=planarOperator a i v)
--       (hu : ∀ i, LocalEqual Sᶜ (entryInjection i u) 0)
--       (hv : ∀ i, LocalEqual Sᶜ (entryInjection i v) 0) : u=v
--   ```
--
--   **Definitions.** The statement is written with `OAI.ElasticityPlanar.Hilbert` (definitions bundle `OAIQ6El002` of this split); `OAI.ElasticityRegularity.LocalEqual` (definitions bundle `OAIQ6El003` of this split); `OAI.ElasticityPlanar.entryInjection` and `OAI.ElasticityPlanar.planarOperator` (definitions bundle `OAIQ6El005` of this split).
--
--   **Used by.** The proofs of `OAI.ElasticityAugmented.supported_matrix_smooth`, `OAI.ElasticityGeneralSlicing.smooth_cylinder_representative` and `OAI_ElasticityPlanar_classical_parameter_smooth` of this split import it.
-- source:
--   OpenAI, Global Uniqueness for the Smooth Isotropic Elasticity Inverse Problem, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 372; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Global-Uniqueness-for-the-Smooth-Isotropic-Elasticity-Inverse-Problem-September-24-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/Elasticity/Supported.lean (declaration OAI.ElasticityPlanar.supported_weak_unique)

import Mathlib
import Definitions.Def_OAIQ6El005

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ElasticityPlanar
open Set MeasureTheory TemperedDistribution
open scoped SchwartzMap ENNReal BigOperators
open ElasticityRegularity
variable {n : Type*} [Fintype n]
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

lemma supported_weak_unique {S : Set ℂ} (hS : IsCompact S)
    (a : n → n → ℂ → ℂ) (ha : ∀ i j, (a i j).HasTemperateGrowth)
    (u v : Hilbert n) (he : ∀ i, planarOperator a i u=planarOperator a i v)
    (hu : ∀ i, LocalEqual Sᶜ (entryInjection i u) 0)
    (hv : ∀ i, LocalEqual Sᶜ (entryInjection i v) 0) : u=v := by
  sorry
end ElasticityPlanar

end

end OAI
end
