-- Prove2me | Theorems.Thm_OAI_ElasticityBoundaryActualTower_finite_tensor_amplitude
-- name    : OAI.ElasticityBoundaryActualTower.finite_tensor_amplitude
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T10:36:19.578004+00:00
-- url     : https://prove2.me/theorems/cf17f0b0-7d31-4d13-ac79-22cce167fc69
-- title:
--   OAI.ElasticityBoundaryActualTower.finite_tensor_amplitude: intermediate lemma from OpenAI, Global Uniqueness for the Smooth Isotropic Elasticity Inverse Problem
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Elasticity.global_uniqueness`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Global Uniqueness for the Smooth Isotropic Elasticity Inverse Problem*, OpenAI Math Release, September 24, 2026, result family 372, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ElasticityBoundaryActualTower.finite_tensor_amplitude` of [lean/OAI/MathematicalPhysics/Elasticity/BoundaryLayers.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/Elasticity/BoundaryLayers.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ElasticityBoundaryActualTower`, with `open scoped BigOperators`, `open MvPolynomial ElasticityBoundaryMVCalculus ElasticityBoundaryMVNormal`):
--
--   ```lean
--   theorem finite_tensor_amplitude (a : Tensor) (b : Lower) (l m : ℂ)
--       (hm : m≠0) (he : l+2*m≠0) (hp : l+3*m≠0)
--       (ha : ∀ i α j β, (a i α j β).coeff 0=C (ElasticityBoundaryLayerOperator.elasticityTensor l m i α j β))
--       (p₀ : W) (h₀ : normal l m p₀=0) (N : ℕ) :
--       ∃ (p : ℕ → W) (R : Polynomial W), p 0=p₀ ∧
--         (∀ n, 0<n → boundary (p n)=0) ∧
--         operator a b (amplitude p N)=Polynomial.X^(N+1)*R
--   ```
--
--   **Definitions.** The statement is written with `OAI.ElasticityBoundaryActualTower.amplitude`, `OAI.ElasticityBoundaryLayerOperator.elasticityTensor`, `OAI.ElasticityBoundaryMVCalculus.MP`, `OAI.ElasticityBoundaryMVNormal.W`, `OAI.ElasticityBoundaryMVNormal.boundary`, `OAI.ElasticityBoundaryMVNormal.normal`, `OAI.ElasticityBoundaryTensorSeries.Lower` and `OAI.ElasticityBoundaryTensorSeries.Tensor` (definitions bundle `OAIQ6El001` of this split); `OAI.ElasticityBoundaryTensorSeries.operator` (definitions bundle `OAIQ6El004` of this split).
--
--   **Used by.** The proof of `OAI.ElasticityBoundaryCutoffParametrix.finite_cutoff_layer` of this split imports it.
-- source:
--   OpenAI, Global Uniqueness for the Smooth Isotropic Elasticity Inverse Problem, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 372; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Global-Uniqueness-for-the-Smooth-Isotropic-Elasticity-Inverse-Problem-September-24-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/Elasticity/BoundaryLayers.lean (declaration OAI.ElasticityBoundaryActualTower.finite_tensor_amplitude)

import Mathlib
import Definitions.Def_OAIQ6El004

section

attribute [-instance] _root_.OAI.ElasticityGeneralSlicing.cylinder_temperate _root_.OAI.ElasticityODE.instFactLeRealOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace ElasticityBoundaryActualTower
open MvPolynomial ElasticityBoundaryMVCalculus ElasticityBoundaryMVNormal
  ElasticityBoundaryTensorSeries ElasticityBoundaryTaylorPolynomial

theorem finite_tensor_amplitude (a : Tensor) (b : Lower) (l m : ℂ)
    (hm : m≠0) (he : l+2*m≠0) (hp : l+3*m≠0)
    (ha : ∀ i α j β, (a i α j β).coeff 0=C (ElasticityBoundaryLayerOperator.elasticityTensor l m i α j β))
    (p₀ : W) (h₀ : normal l m p₀=0) (N : ℕ) :
    ∃ (p : ℕ → W) (R : Polynomial W), p 0=p₀ ∧
      (∀ n, 0<n → boundary (p n)=0) ∧
      operator a b (amplitude p N)=Polynomial.X^(N+1)*R := by
  sorry

end ElasticityBoundaryActualTower

end
end

end OAI
end
