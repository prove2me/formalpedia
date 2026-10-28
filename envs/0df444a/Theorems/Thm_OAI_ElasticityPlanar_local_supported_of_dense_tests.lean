-- Prove2me | Theorems.Thm_OAI_ElasticityPlanar_local_supported_of_dense_tests
-- name    : OAI.ElasticityPlanar.local_supported_of_dense_tests
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T10:41:02.157474+00:00
-- url     : https://prove2.me/theorems/dd7b5be8-7aa2-406b-b0c8-802ffa959d18
-- title:
--   OAI.ElasticityPlanar.local_supported_of_dense_tests: intermediate lemma from OpenAI, Global Uniqueness for the Smooth Isotropic Elasticity Inverse Problem
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Elasticity.global_uniqueness`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Global Uniqueness for the Smooth Isotropic Elasticity Inverse Problem*, OpenAI Math Release, September 24, 2026, result family 372, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ElasticityPlanar.local_supported_of_dense_tests` of [lean/OAI/MathematicalPhysics/Elasticity/Supported.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/Elasticity/Supported.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ElasticityPlanar`, with `open Set MeasureTheory TemperedDistribution`, `open scoped ENNReal SchwartzMap BigOperators`, `open ElasticityRegularity`):
--
--   ```lean
--   theorem local_supported_of_dense_tests {S K : Set ℂ} (hS : IsCompact S) (hK : IsCompact K)
--       (a : n → n → P × ℂ → ℂ) (ha : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (a i j))
--       (hs : ∀ i j p z, z∉K → a i j (p,z)=0)
--       (f : P → Hilbert n) (hf : ContDiff ℝ (⊤ : ℕ∞) f) {D : Set P} (hD : Dense D)
--       (hex : ∀ p∈D, ∃ v : n → Test, (∀ i, tsupport (v i : ℂ → ℂ)⊆S) ∧
--         ∀ i, planarOperator (fun i j z => a i j (p,z)) i (embed v)=entryInjection i (f p))
--       (p₀ : P) :
--       ∃ (U : Set P) (u : P → Hilbert n), IsOpen U ∧ p₀∈U ∧
--         ContDiffOn ℝ (⊤ : ℕ∞) u U ∧ ∀ p∈U, ∀ i,
--           planarOperator (fun i j z => a i j (p,z)) i (u p)=entryInjection i (f p) ∧
--           LocalEqual Sᶜ (entryInjection i (u p)) 0
--   ```
--
--   **Definitions.** The statement is written with `OAI.ElasticityPlanar.Hilbert`, `OAI.ElasticityPlanar.Test` and `OAI.ElasticityPlanar.embed` (definitions bundle `OAIQ6El002` of this split); `OAI.ElasticityRegularity.LocalEqual` (definitions bundle `OAIQ6El003` of this split); `OAI.ElasticityPlanar.entryInjection` and `OAI.ElasticityPlanar.planarOperator` (definitions bundle `OAIQ6El005` of this split).
--
--   **Used by.** The proof of `OAI.ElasticityPlanar.global_supported_of_dense` of this split imports it.
-- source:
--   OpenAI, Global Uniqueness for the Smooth Isotropic Elasticity Inverse Problem, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 372; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Global-Uniqueness-for-the-Smooth-Isotropic-Elasticity-Inverse-Problem-September-24-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/Elasticity/Supported.lean (declaration OAI.ElasticityPlanar.local_supported_of_dense_tests)

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
open scoped ENNReal SchwartzMap BigOperators
open ElasticityRegularity
variable {n : Type*} [Fintype n]
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

theorem local_supported_of_dense_tests {S K : Set ℂ} (hS : IsCompact S) (hK : IsCompact K)
    (a : n → n → P × ℂ → ℂ) (ha : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (a i j))
    (hs : ∀ i j p z, z∉K → a i j (p,z)=0)
    (f : P → Hilbert n) (hf : ContDiff ℝ (⊤ : ℕ∞) f) {D : Set P} (hD : Dense D)
    (hex : ∀ p∈D, ∃ v : n → Test, (∀ i, tsupport (v i : ℂ → ℂ)⊆S) ∧
      ∀ i, planarOperator (fun i j z => a i j (p,z)) i (embed v)=entryInjection i (f p))
    (p₀ : P) :
    ∃ (U : Set P) (u : P → Hilbert n), IsOpen U ∧ p₀∈U ∧
      ContDiffOn ℝ (⊤ : ℕ∞) u U ∧ ∀ p∈U, ∀ i,
        planarOperator (fun i j z => a i j (p,z)) i (u p)=entryInjection i (f p) ∧
        LocalEqual Sᶜ (entryInjection i (u p)) 0 := by
  sorry
end ElasticityPlanar

end

end OAI
end
