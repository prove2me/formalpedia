-- Prove2me | Theorems.Thm_OAI_ElasticityBoundaryCutoffParametrix_finite_cutoff_layer
-- name    : OAI.ElasticityBoundaryCutoffParametrix.finite_cutoff_layer
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T10:19:47.150211+00:00
-- url     : https://prove2.me/theorems/b24a0970-1b9d-47cc-a4cf-07c73bf7920a
-- title:
--   OAI.ElasticityBoundaryCutoffParametrix.finite_cutoff_layer: intermediate lemma from OpenAI, Global Uniqueness for the Smooth Isotropic Elasticity Inverse Problem
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Elasticity.global_uniqueness`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Global Uniqueness for the Smooth Isotropic Elasticity Inverse Problem*, OpenAI Math Release, September 24, 2026, result family 372, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ElasticityBoundaryCutoffParametrix.finite_cutoff_layer` of [lean/OAI/MathematicalPhysics/Elasticity/BoundaryParametrix.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/Elasticity/BoundaryParametrix.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ElasticityBoundaryCutoffParametrix`, with `open Set MeasureTheory Filter`, `open scoped BigOperators Topology`, `open MvPolynomial ElasticityBoundaryMVCalculus ElasticityBoundaryMVNormal`):
--
--   ```lean
--   theorem finite_cutoff_layer (a : SmoothTensor) (b : SmoothLower)
--       (ha : ∀ i α j β, ContDiff ℝ (⊤ : ℕ∞) (a i α j β) ∧ HasCompactSupport (a i α j β))
--       (hb : ∀ i j β, ContDiff ℝ (⊤ : ℕ∞) (b i j β) ∧ HasCompactSupport (b i j β))
--       {χ : Y → ℂ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hc : HasCompactSupport χ)
--       (hχ0 : χ =ᶠ[𝓝 (0:Y)] fun _ => 1)
--       (l m : ℂ) (hm : m≠0) (he : l+2*m≠0) (hp : l+3*m≠0)
--       (ha0 : ∀ i α j β, a i α j β 0=elasticityTensor l m i α j β)
--       (p₀ : W) (h₀ : normal l m p₀=0) (N : ℕ) :
--       ∃ p : ℕ → W, p 0=p₀ ∧ (∀ n, 0<n → boundary (p n)=0) ∧
--         ∀ i : Fin 3, ∃ C : ℝ, 0≤C ∧ ∀ δ : ℝ, 0<δ → δ≤1 →
--           MemLp (strong a b (cutoffLayer χ (amplitude p (N+1)) δ) i) 2 (volume.restrict halfspace) ∧
--           (∫ z in halfspace, ‖strong a b (cutoffLayer χ (amplitude p (N+1)) δ) i z‖^2) ≤ C*δ^(2*N)
--   ```
--
--   **Definitions.** The statement is written with `OAI.ElasticityBoundaryActualTower.amplitude`, `OAI.ElasticityBoundaryCutoffLayer.cutoffLayer`, `OAI.ElasticityBoundaryCutoffParametrix.Y`, `OAI.ElasticityBoundaryLayerOperator.elasticityTensor`, `OAI.ElasticityBoundaryMVCalculus.MP`, `OAI.ElasticityBoundaryMVNormal.W`, `OAI.ElasticityBoundaryMVNormal.boundary`, `OAI.ElasticityBoundaryMVNormal.normal`, `OAI.ElasticityBoundaryProfileBounds.Y`, `OAI.ElasticityBoundaryProfileBounds.halfspace`, `OAI.ElasticityBoundarySmoothOperator.SmoothLower`, `OAI.ElasticityBoundarySmoothOperator.SmoothTensor`, `OAI.ElasticityBoundarySmoothOperator.Y`, `OAI.ElasticityBoundaryStrongLayer.Y` and `OAI.ElasticityBoundaryStrongLayer.strong` (definitions bundle `OAIQ6El001` of this split).
--
--   **Used by.** The proofs of `OAI_ElasticityBoundaryPacket_Setup_field_force_mass` and `OAI.ElasticityBoundaryPacket.Setup.packet` of this split import it.
-- source:
--   OpenAI, Global Uniqueness for the Smooth Isotropic Elasticity Inverse Problem, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 372; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Global-Uniqueness-for-the-Smooth-Isotropic-Elasticity-Inverse-Problem-September-24-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/Elasticity/BoundaryParametrix.lean (declaration OAI.ElasticityBoundaryCutoffParametrix.finite_cutoff_layer)

import Mathlib
import Definitions.Def_OAIQ6El001

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators Topology
namespace ElasticityBoundaryCutoffParametrix
open MvPolynomial ElasticityBoundaryMVCalculus ElasticityBoundaryMVNormal
  ElasticityBoundaryParameter ElasticityBoundaryParameterBounds ElasticityBoundaryTensorSeries
  ElasticityBoundaryActualTower ElasticityBoundarySmoothOperator ElasticityBoundaryProfile
  ElasticityBoundaryProfileBounds ElasticityBoundaryScaling ElasticityBoundaryLayerOperator
  ElasticityBoundaryWeights ElasticityBoundaryStrongLayer ElasticityBoundaryOrderBound
  ElasticityBoundaryCutoffBound ElasticityBoundaryCutoffLayer

theorem finite_cutoff_layer (a : SmoothTensor) (b : SmoothLower)
    (ha : ∀ i α j β, ContDiff ℝ (⊤ : ℕ∞) (a i α j β) ∧ HasCompactSupport (a i α j β))
    (hb : ∀ i j β, ContDiff ℝ (⊤ : ℕ∞) (b i j β) ∧ HasCompactSupport (b i j β))
    {χ : Y → ℂ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hc : HasCompactSupport χ)
    (hχ0 : χ =ᶠ[𝓝 (0:Y)] fun _ => 1)
    (l m : ℂ) (hm : m≠0) (he : l+2*m≠0) (hp : l+3*m≠0)
    (ha0 : ∀ i α j β, a i α j β 0=elasticityTensor l m i α j β)
    (p₀ : W) (h₀ : normal l m p₀=0) (N : ℕ) :
    ∃ p : ℕ → W, p 0=p₀ ∧ (∀ n, 0<n → boundary (p n)=0) ∧
      ∀ i : Fin 3, ∃ C : ℝ, 0≤C ∧ ∀ δ : ℝ, 0<δ → δ≤1 →
        MemLp (strong a b (cutoffLayer χ (amplitude p (N+1)) δ) i) 2 (volume.restrict halfspace) ∧
        (∫ z in halfspace, ‖strong a b (cutoffLayer χ (amplitude p (N+1)) δ) i z‖^2) ≤ C*δ^(2*N) := by
  sorry

end ElasticityBoundaryCutoffParametrix

end
end

end OAI
end
