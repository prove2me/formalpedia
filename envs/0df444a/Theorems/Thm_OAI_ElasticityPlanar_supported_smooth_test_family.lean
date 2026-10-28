-- Prove2me | Theorems.Thm_OAI_ElasticityPlanar_supported_smooth_test_family
-- name    : OAI.ElasticityPlanar.supported_smooth_test_family
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T10:41:25.275143+00:00
-- url     : https://prove2.me/theorems/f7e45e41-36f4-49a6-be6c-468ddd3e3df4
-- title:
--   OAI.ElasticityPlanar.supported_smooth_test_family: intermediate lemma from OpenAI, Global Uniqueness for the Smooth Isotropic Elasticity Inverse Problem
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Elasticity.global_uniqueness`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Global Uniqueness for the Smooth Isotropic Elasticity Inverse Problem*, OpenAI Math Release, September 24, 2026, result family 372, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ElasticityPlanar.supported_smooth_test_family` of [lean/OAI/MathematicalPhysics/Elasticity/Supported.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/Elasticity/Supported.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ElasticityPlanar`, with `open Set MeasureTheory TemperedDistribution`, `open scoped SchwartzMap ENNReal BigOperators`, `open ElasticityRegularity`):
--
--   ```lean
--   lemma supported_smooth_test_family {S : Set ℂ} (hS : IsCompact S)
--       (u : P → Lp ℂ 2 (volume : Measure ℂ))
--       (hu : ∀ N : ℕ, SmoothLocalSobolev univ N (fun p => (u p : 𝓢'(ℂ,ℂ))))
--       (hs : ∀ p, LocalEqual Sᶜ (u p : 𝓢'(ℂ,ℂ)) 0) :
--       ∃ v : P → Test, ContDiff ℝ (⊤ : ℕ∞) (fun q : P × ℂ => v q.1 q.2) ∧
--         ∀ p, L2 (v p)=u p ∧ tsupport (v p : ℂ → ℂ)⊆S
--   ```
--
--   **Definitions.** The statement is written with `OAI.ElasticityPlanar.L2` and `OAI.ElasticityPlanar.Test` (definitions bundle `OAIQ6El002` of this split); `OAI.ElasticityRegularity.LocalEqual` (definitions bundle `OAIQ6El003` of this split); `OAI.ElasticityRegularity.SmoothLocalSobolev` (definitions bundle `OAIQ6El005` of this split).
--
--   **Used by.** The proofs of `OAI_ElasticityPlanar_classical_parameter_smooth` and `OAI.ElasticityPlanar.supported_parameter_inversion` of this split import it.
-- source:
--   OpenAI, Global Uniqueness for the Smooth Isotropic Elasticity Inverse Problem, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 372; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Global-Uniqueness-for-the-Smooth-Isotropic-Elasticity-Inverse-Problem-September-24-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/Elasticity/Supported.lean (declaration OAI.ElasticityPlanar.supported_smooth_test_family)

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

lemma supported_smooth_test_family {S : Set ℂ} (hS : IsCompact S)
    (u : P → Lp ℂ 2 (volume : Measure ℂ))
    (hu : ∀ N : ℕ, SmoothLocalSobolev univ N (fun p => (u p : 𝓢'(ℂ,ℂ))))
    (hs : ∀ p, LocalEqual Sᶜ (u p : 𝓢'(ℂ,ℂ)) 0) :
    ∃ v : P → Test, ContDiff ℝ (⊤ : ℕ∞) (fun q : P × ℂ => v q.1 q.2) ∧
      ∀ p, L2 (v p)=u p ∧ tsupport (v p : ℂ → ℂ)⊆S := by
  sorry
end ElasticityPlanar

end

end OAI
end
