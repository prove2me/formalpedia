-- Prove2me | Theorems.Thm_OAI_ElasticityPlanar_local_graph_solution
-- name    : OAI.ElasticityPlanar.local_graph_solution
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T10:41:11.566748+00:00
-- url     : https://prove2.me/theorems/703c6963-6eac-4665-b717-5e2defe985c9
-- title:
--   OAI.ElasticityPlanar.local_graph_solution: intermediate lemma from OpenAI, Global Uniqueness for the Smooth Isotropic Elasticity Inverse Problem
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Elasticity.global_uniqueness`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Global Uniqueness for the Smooth Isotropic Elasticity Inverse Problem*, OpenAI Math Release, September 24, 2026, result family 372, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ElasticityPlanar.local_graph_solution` of [lean/OAI/MathematicalPhysics/Elasticity/Supported.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/Elasticity/Supported.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ElasticityPlanar`, with `open Set MeasureTheory TemperedDistribution`, `open scoped ENNReal SchwartzMap BigOperators`, `open ElasticityRegularity`):
--
--   ```lean
--   lemma local_graph_solution {S : Set ℂ} (hS : IsCompact S)
--       (a : n → n → ℂ → ℂ) (ha : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (a i j))
--       (A : P → closedGraph S a ha →L[ℂ] Hilbert n)
--       (hA : ContDiff ℝ (⊤ : ℕ∞) A) (p₀ : P) (hA₀ : A p₀=graphSecond S a ha)
--       (f : P → Hilbert n) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
--       {D : Set P} (hD : Dense D) (hex : ∀ p∈D, ∃ u : closedGraph S a ha, A p u=f p) :
--       ∃ (U : Set P) (u : P → closedGraph S a ha), IsOpen U ∧ p₀∈U ∧
--         ContDiffOn ℝ (⊤ : ℕ∞) u U ∧ ∀ p∈U, A p (u p)=f p
--   ```
--
--   **Definitions.** The statement is written with `OAI.ElasticityPlanar.Hilbert` (definitions bundle `OAIQ6El002` of this split); `OAI.ElasticityPlanar.GraphSpace`, `OAI.ElasticityPlanar.closedGraph` and `OAI.ElasticityPlanar.graphSecond` (definitions bundle `OAIQ6El005` of this split).
--
--   **Used by.** The proof of `OAI.ElasticityPlanar.local_supported_of_dense_tests` of this split imports it.
-- source:
--   OpenAI, Global Uniqueness for the Smooth Isotropic Elasticity Inverse Problem, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 372; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Global-Uniqueness-for-the-Smooth-Isotropic-Elasticity-Inverse-Problem-September-24-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/Elasticity/Supported.lean (declaration OAI.ElasticityPlanar.local_graph_solution)

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

omit [FiniteDimensional ℝ P] in
lemma local_graph_solution {S : Set ℂ} (hS : IsCompact S)
    (a : n → n → ℂ → ℂ) (ha : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (a i j))
    (A : P → closedGraph S a ha →L[ℂ] Hilbert n)
    (hA : ContDiff ℝ (⊤ : ℕ∞) A) (p₀ : P) (hA₀ : A p₀=graphSecond S a ha)
    (f : P → Hilbert n) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    {D : Set P} (hD : Dense D) (hex : ∀ p∈D, ∃ u : closedGraph S a ha, A p u=f p) :
    ∃ (U : Set P) (u : P → closedGraph S a ha), IsOpen U ∧ p₀∈U ∧
      ContDiffOn ℝ (⊤ : ℕ∞) u U ∧ ∀ p∈U, A p (u p)=f p := by
  sorry

end ElasticityPlanar

end

end OAI
end
