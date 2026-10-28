-- Prove2me | Theorems.Thm_OAI_ElasticityPlanar_global_supported_of_dense
-- name    : OAI.ElasticityPlanar.global_supported_of_dense
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T10:40:50.992691+00:00
-- url     : https://prove2.me/theorems/dbdf3db3-53a1-47d3-ae54-146387ac6a0d
-- title:
--   OAI.ElasticityPlanar.global_supported_of_dense: intermediate lemma from OpenAI, Global Uniqueness for the Smooth Isotropic Elasticity Inverse Problem
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Elasticity.global_uniqueness`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Global Uniqueness for the Smooth Isotropic Elasticity Inverse Problem*, OpenAI Math Release, September 24, 2026, result family 372, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ElasticityPlanar.global_supported_of_dense` of [lean/OAI/MathematicalPhysics/Elasticity/Supported.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/Elasticity/Supported.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ElasticityPlanar`, with `open MeasureTheory TemperedDistribution Set`, `open scoped SchwartzMap ENNReal BigOperators Manifold`, `open ElasticityRegularity`):
--
--   ```lean
--   theorem global_supported_of_dense {S K : Set ℂ} (hS : IsCompact S) (hK : IsCompact K)
--       (a : n → n → P × ℂ → ℂ) (ha : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (a i j))
--       (hs : ∀ i j p z, z∉K → a i j (p,z)=0)
--       (F : P → n → 𝓢(ℂ,ℂ)) (f : P → Hilbert n)
--       (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hFe : ∀ p i, entryInjection i (f p)=(F p i : 𝓢'(ℂ,ℂ)))
--       {D : Set P} (hD : Dense D)
--       (hex : ∀ p∈D, ∃ w : Hilbert n, ∀ i,
--         planarOperator (fun i j z => a i j (p,z)) i w=entryInjection i (f p) ∧
--         LocalEqual Sᶜ (entryInjection i w) 0) :
--       ∃ u : P → Hilbert n, ContDiff ℝ (⊤ : ℕ∞) u ∧ ∀ p i,
--         planarOperator (fun i j z => a i j (p,z)) i (u p)=entryInjection i (f p) ∧
--         LocalEqual Sᶜ (entryInjection i (u p)) 0
--   ```
--
--   **Definitions.** The statement is written with `OAI.ElasticityPlanar.Hilbert` (definitions bundle `OAIQ6El002` of this split); `OAI.ElasticityRegularity.LocalEqual` (definitions bundle `OAIQ6El003` of this split); `OAI.ElasticityPlanar.entryInjection` and `OAI.ElasticityPlanar.planarOperator` (definitions bundle `OAIQ6El005` of this split).
--
--   **Used by.** The proofs of `OAI_ElasticityPlanar_classical_parameter_smooth` and `OAI.ElasticityPlanar.supported_parameter_inversion` of this split import it.
-- source:
--   OpenAI, Global Uniqueness for the Smooth Isotropic Elasticity Inverse Problem, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 372; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Global-Uniqueness-for-the-Smooth-Isotropic-Elasticity-Inverse-Problem-September-24-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/Elasticity/Supported.lean (declaration OAI.ElasticityPlanar.global_supported_of_dense)

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
open MeasureTheory TemperedDistribution Set
open scoped SchwartzMap ENNReal BigOperators Manifold
open ElasticityRegularity
variable {n : Type*} [Fintype n]
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

theorem global_supported_of_dense {S K : Set ℂ} (hS : IsCompact S) (hK : IsCompact K)
    (a : n → n → P × ℂ → ℂ) (ha : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (a i j))
    (hs : ∀ i j p z, z∉K → a i j (p,z)=0)
    (F : P → n → 𝓢(ℂ,ℂ)) (f : P → Hilbert n)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hFe : ∀ p i, entryInjection i (f p)=(F p i : 𝓢'(ℂ,ℂ)))
    {D : Set P} (hD : Dense D)
    (hex : ∀ p∈D, ∃ w : Hilbert n, ∀ i,
      planarOperator (fun i j z => a i j (p,z)) i w=entryInjection i (f p) ∧
      LocalEqual Sᶜ (entryInjection i w) 0) :
    ∃ u : P → Hilbert n, ContDiff ℝ (⊤ : ℕ∞) u ∧ ∀ p i,
      planarOperator (fun i j z => a i j (p,z)) i (u p)=entryInjection i (f p) ∧
      LocalEqual Sᶜ (entryInjection i (u p)) 0 := by
  sorry
end ElasticityPlanar

end

end OAI
end
