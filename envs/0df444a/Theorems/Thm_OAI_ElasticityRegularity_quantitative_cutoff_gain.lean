-- Prove2me | Theorems.Thm_OAI_ElasticityRegularity_quantitative_cutoff_gain
-- name    : OAI.ElasticityRegularity.quantitative_cutoff_gain
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T10:30:26.261184+00:00
-- url     : https://prove2.me/theorems/20aa347e-35cd-4c5a-92d1-c8f76acefb8b
-- title:
--   OAI.ElasticityRegularity.quantitative_cutoff_gain: intermediate lemma from OpenAI, Global Uniqueness for the Smooth Isotropic Elasticity Inverse Problem
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Elasticity.global_uniqueness`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Global Uniqueness for the Smooth Isotropic Elasticity Inverse Problem*, OpenAI Math Release, September 24, 2026, result family 372, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ElasticityRegularity.quantitative_cutoff_gain` of [lean/OAI/MathematicalPhysics/Elasticity/CGO.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/Elasticity/CGO.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ElasticityRegularity`, with `open MeasureTheory TemperedDistribution`, `open scoped SchwartzMap LineDeriv Laplacian Real ENNReal BigOperators`):
--
--   ```lean
--   theorem quantitative_cutoff_gain (k : ℤ) {χ η : E → ℂ}
--       (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hcχ : HasCompactSupport χ)
--       (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hcη : HasCompactSupport η)
--       (h1 : Set.EqOn η 1 (tsupport χ)) :
--       ∃ C : ℝ, 0<C ∧ ∀ (u : 𝓢'(E,ℂ)) (f g : Lp ℂ 2 (volume : Measure E)),
--         sobolevInjection (k : ℝ) f=smulLeftCLM ℂ η u →
--         sobolevInjection ((k : ℝ)-1) g=smulLeftCLM ℂ η (Δ u) →
--         ∃ q : Lp ℂ 2 (volume : Measure E),
--           sobolevInjection ((k : ℝ)+1) q=smulLeftCLM ℂ χ u ∧
--           ‖q‖ ≤ C*(‖f‖+‖g‖)
--   ```
--
--   **Definitions.** The statement is written with `OAI.ElasticityRegularity.sobolevInjection` (definitions bundle `OAIQ6El002` of this split).
--
--   **Used by.** The proof of `OAI.ElasticityDistribution.scalar_principal_quantitative_gain` of this split imports it.
-- source:
--   OpenAI, Global Uniqueness for the Smooth Isotropic Elasticity Inverse Problem, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 372; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Global-Uniqueness-for-the-Smooth-Isotropic-Elasticity-Inverse-Problem-September-24-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/Elasticity/CGO.lean (declaration OAI.ElasticityRegularity.quantitative_cutoff_gain)

import Mathlib
import Definitions.Def_OAIQ6El002

section

attribute [-instance] _root_.OAI.ElasticityGeneralSlicing.cylinder_temperate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ElasticityRegularity
open MeasureTheory TemperedDistribution
open scoped SchwartzMap LineDeriv Laplacian Real ENNReal BigOperators
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem quantitative_cutoff_gain (k : ℤ) {χ η : E → ℂ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hcχ : HasCompactSupport χ)
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hcη : HasCompactSupport η)
    (h1 : Set.EqOn η 1 (tsupport χ)) :
    ∃ C : ℝ, 0<C ∧ ∀ (u : 𝓢'(E,ℂ)) (f g : Lp ℂ 2 (volume : Measure E)),
      sobolevInjection (k : ℝ) f=smulLeftCLM ℂ η u →
      sobolevInjection ((k : ℝ)-1) g=smulLeftCLM ℂ η (Δ u) →
      ∃ q : Lp ℂ 2 (volume : Measure E),
        sobolevInjection ((k : ℝ)+1) q=smulLeftCLM ℂ χ u ∧
        ‖q‖ ≤ C*(‖f‖+‖g‖) := by
  sorry
end ElasticityRegularity

end

end OAI
end
