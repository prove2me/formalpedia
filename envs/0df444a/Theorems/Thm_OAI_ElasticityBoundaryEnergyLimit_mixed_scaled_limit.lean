-- Prove2me | Theorems.Thm_OAI_ElasticityBoundaryEnergyLimit_mixed_scaled_limit
-- name    : OAI.ElasticityBoundaryEnergyLimit.mixed_scaled_limit
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T10:20:03.98081+00:00
-- url     : https://prove2.me/theorems/f12e6265-1dd7-4196-97ec-532c5c2cd5f3
-- title:
--   OAI.ElasticityBoundaryEnergyLimit.mixed_scaled_limit: intermediate lemma from OpenAI, Global Uniqueness for the Smooth Isotropic Elasticity Inverse Problem
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Elasticity.global_uniqueness`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Global Uniqueness for the Smooth Isotropic Elasticity Inverse Problem*, OpenAI Math Release, September 24, 2026, result family 372, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ElasticityBoundaryEnergyLimit.mixed_scaled_limit` of [lean/OAI/MathematicalPhysics/Elasticity/BoundaryEnergy.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/Elasticity/BoundaryEnergy.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ElasticityBoundaryEnergyLimit`, with `open Set Filter MeasureTheory`, `open scoped Topology BigOperators`, `open MvPolynomial ElasticityBoundaryMVCalculus ElasticityBoundaryMVNormal`):
--
--   ```lean
--   theorem mixed_scaled_limit (n : ℕ) {H χ : Y → ℂ} (hH : Continuous H) (hcH : HasCompactSupport H)
--       (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hcχ : HasCompactSupport χ) (h0 : χ 0=1)
--       (p q : Polynomial W) (i α j β : Fin 3) :
--       Tendsto (fun δ => ∫ y, weight 2 y • mixedScaled n H χ p q i α j β δ y) (𝓝[>] 0)
--         (𝓝 (∫ y : Y, weight 2 y • ((y 2:ℂ)^n*H 0*
--           value (E₀ α (p.coeff 0 i)) y*star (value (E₀ β (q.coeff 0 j)) y))))
--   ```
--
--   **Definitions.** The statement is written with `OAI.ElasticityBoundaryEnergyLimit.Y`, `OAI.ElasticityBoundaryEnergyLimit.mixedScaled`, `OAI.ElasticityBoundaryMVCalculus.MP`, `OAI.ElasticityBoundaryMVCalculus.value`, `OAI.ElasticityBoundaryMVNormal.W`, `OAI.ElasticityBoundaryParameter.E₀`, `OAI.ElasticityBoundaryWeights.Y` and `OAI.ElasticityBoundaryWeights.weight` (definitions bundle `OAIQ6El001` of this split).
--
--   **Used by.** The proof of `OAI.ElasticityBoundaryMixedScaling.mixedEnergy_limit` of this split imports it.
-- source:
--   OpenAI, Global Uniqueness for the Smooth Isotropic Elasticity Inverse Problem, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 372; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Global-Uniqueness-for-the-Smooth-Isotropic-Elasticity-Inverse-Problem-September-24-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/Elasticity/BoundaryEnergy.lean (declaration OAI.ElasticityBoundaryEnergyLimit.mixed_scaled_limit)

import Mathlib
import Definitions.Def_OAIQ6El001

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ElasticityBoundaryEnergyLimit

open Set Filter MeasureTheory
open scoped Topology BigOperators
open MvPolynomial ElasticityBoundaryMVCalculus ElasticityBoundaryMVNormal
  ElasticityBoundaryScaling ElasticityBoundaryWeights ElasticityBoundaryOrderBound
  ElasticityBoundaryParameter ElasticityBoundaryParameterBounds ElasticityBoundaryTensorSeries
  ElasticityBoundaryActualTower ElasticityBoundaryCutoffParametrix ElasticityBoundaryLimit
  ElasticityBoundaryProfileBounds ElasticityBoundaryCutoffLayer ElasticityBoundaryProfile
  ElasticityBoundaryCutoffBound

theorem mixed_scaled_limit (n : ℕ) {H χ : Y → ℂ} (hH : Continuous H) (hcH : HasCompactSupport H)
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hcχ : HasCompactSupport χ) (h0 : χ 0=1)
    (p q : Polynomial W) (i α j β : Fin 3) :
    Tendsto (fun δ => ∫ y, weight 2 y • mixedScaled n H χ p q i α j β δ y) (𝓝[>] 0)
      (𝓝 (∫ y : Y, weight 2 y • ((y 2:ℂ)^n*H 0*
        value (E₀ α (p.coeff 0 i)) y*star (value (E₀ β (q.coeff 0 j)) y)))) := by
  sorry

end ElasticityBoundaryEnergyLimit

end

end OAI
end
