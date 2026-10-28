-- Prove2me | Theorems.Thm_OAI_ElasticityBoundaryMixedScaling_mixedEnergy_limit
-- name    : OAI.ElasticityBoundaryMixedScaling.mixedEnergy_limit
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T10:20:49.940014+00:00
-- url     : https://prove2.me/theorems/93ab957b-bf42-4c4b-bac4-9d9cc7f639af
-- title:
--   OAI.ElasticityBoundaryMixedScaling.mixedEnergy_limit: intermediate lemma from OpenAI, Global Uniqueness for the Smooth Isotropic Elasticity Inverse Problem
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Elasticity.global_uniqueness`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Global Uniqueness for the Smooth Isotropic Elasticity Inverse Problem*, OpenAI Math Release, September 24, 2026, result family 372, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ElasticityBoundaryMixedScaling.mixedEnergy_limit` of [lean/OAI/MathematicalPhysics/Elasticity/BoundaryEnergy.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/Elasticity/BoundaryEnergy.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ElasticityBoundaryMixedScaling`, with `open Set Filter MeasureTheory`, `open scoped Topology BigOperators`, `open MvPolynomial ElasticityBoundaryMVCalculus ElasticityBoundaryMVNormal`):
--
--   ```lean
--   theorem mixedEnergy_limit (n : ℕ) {H χ : Y → ℂ} (hH : Continuous H) (hcH : HasCompactSupport H)
--       (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hcχ : HasCompactSupport χ) (h0 : χ 0=1)
--       (p q : Polynomial W) (i α j β : Fin 3) :
--       Tendsto (fun δ => ((δ^(2*n))⁻¹:ℝ) • mixedEnergy n H χ p q i α j β δ) (𝓝[>] 0)
--         (𝓝 (∫ y : Y, weight 2 y • ((y 2:ℂ)^n*H 0*
--           value (E₀ α (p.coeff 0 i)) y*star (value (E₀ β (q.coeff 0 j)) y))))
--   ```
--
--   **Definitions.** The statement is written with `OAI.ElasticityBoundaryMVCalculus.MP`, `OAI.ElasticityBoundaryMVCalculus.value`, `OAI.ElasticityBoundaryMVNormal.W`, `OAI.ElasticityBoundaryMixedScaling.Y`, `OAI.ElasticityBoundaryMixedScaling.mixedEnergy`, `OAI.ElasticityBoundaryParameter.E₀` and `OAI.ElasticityBoundaryWeights.weight` (definitions bundle `OAIQ6El001` of this split).
--
--   **Used by.** The proof of `OAI.ElasticityBoundaryPacket.Setup.extract_normal` of this split imports it.
-- source:
--   OpenAI, Global Uniqueness for the Smooth Isotropic Elasticity Inverse Problem, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 372; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Global-Uniqueness-for-the-Smooth-Isotropic-Elasticity-Inverse-Problem-September-24-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/Elasticity/BoundaryEnergy.lean (declaration OAI.ElasticityBoundaryMixedScaling.mixedEnergy_limit)

import Mathlib
import Definitions.Def_OAIQ6El001

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ElasticityBoundaryMixedScaling

open Set Filter MeasureTheory
open scoped Topology BigOperators
open MvPolynomial ElasticityBoundaryMVCalculus ElasticityBoundaryMVNormal
  ElasticityBoundaryScaling ElasticityBoundaryWeights ElasticityBoundaryOrderBound
  ElasticityBoundaryParameter ElasticityBoundaryParameterBounds ElasticityBoundaryTensorSeries
  ElasticityBoundaryActualTower ElasticityBoundaryCutoffParametrix ElasticityBoundaryLimit
  ElasticityBoundaryProfileBounds ElasticityBoundaryCutoffLayer ElasticityBoundaryProfile
  ElasticityBoundaryCutoffBound ElasticityBoundaryEnergyLimit ElasticityBoundaryStrongLayer

theorem mixedEnergy_limit (n : ℕ) {H χ : Y → ℂ} (hH : Continuous H) (hcH : HasCompactSupport H)
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hcχ : HasCompactSupport χ) (h0 : χ 0=1)
    (p q : Polynomial W) (i α j β : Fin 3) :
    Tendsto (fun δ => ((δ^(2*n))⁻¹:ℝ) • mixedEnergy n H χ p q i α j β δ) (𝓝[>] 0)
      (𝓝 (∫ y : Y, weight 2 y • ((y 2:ℂ)^n*H 0*
        value (E₀ α (p.coeff 0 i)) y*star (value (E₀ β (q.coeff 0 j)) y)))) := by
  sorry

end ElasticityBoundaryMixedScaling

end

end OAI
end
