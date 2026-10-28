-- Prove2me | Theorems.Thm_OAI_ElasticityBoundarySmoothOperator_scaledOperator_order_bound
-- name    : OAI.ElasticityBoundarySmoothOperator.scaledOperator_order_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T10:36:49.092365+00:00
-- url     : https://prove2.me/theorems/718c1fb9-a351-4fd9-b8e3-a4930502c253
-- title:
--   OAI.ElasticityBoundarySmoothOperator.scaledOperator_order_bound: intermediate lemma from OpenAI, Global Uniqueness for the Smooth Isotropic Elasticity Inverse Problem
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Elasticity.global_uniqueness`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Global Uniqueness for the Smooth Isotropic Elasticity Inverse Problem*, OpenAI Math Release, September 24, 2026, result family 372, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ElasticityBoundarySmoothOperator.scaledOperator_order_bound` of [lean/OAI/MathematicalPhysics/Elasticity/BoundaryLayers.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/Elasticity/BoundaryLayers.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ElasticityBoundarySmoothOperator`, with `open Set MeasureTheory`, `open scoped BigOperators`, `open MvPolynomial ElasticityBoundaryMVCalculus ElasticityBoundaryMVNormal`):
--
--   ```lean
--   lemma scaledOperator_order_bound (a : SmoothTensor) (b : SmoothLower)
--       (ha : ∀ i α j β, ContDiff ℝ (⊤ : ℕ∞) (a i α j β) ∧ HasCompactSupport (a i α j β))
--       (hb : ∀ i j β, ContDiff ℝ (⊤ : ℕ∞) (b i j β) ∧ HasCompactSupport (b i j β))
--       (q R : Polynomial W) (N : ℕ)
--       (hR : operator (tensorTaylor a N) (lowerTaylor b N) q=Polynomial.X^(N+1)*R)
--       (i : Fin 3) : OrderBound (fun δ y => scaledOperator a b q δ i y) (N+1)
--   ```
--
--   **Definitions.** The statement is written with `OAI.ElasticityBoundaryMVCalculus.MP`, `OAI.ElasticityBoundaryMVNormal.W`, `OAI.ElasticityBoundaryOrderBound.OrderBound`, `OAI.ElasticityBoundaryOrderBound.Y`, `OAI.ElasticityBoundarySmoothOperator.SmoothLower`, `OAI.ElasticityBoundarySmoothOperator.SmoothTensor`, `OAI.ElasticityBoundarySmoothOperator.Y`, `OAI.ElasticityBoundarySmoothOperator.lowerTaylor`, `OAI.ElasticityBoundarySmoothOperator.scaledOperator` and `OAI.ElasticityBoundarySmoothOperator.tensorTaylor` (definitions bundle `OAIQ6El001` of this split); `OAI.ElasticityBoundaryTensorSeries.operator` (definitions bundle `OAIQ6El004` of this split).
--
--   **Used by.** The proof of `OAI.ElasticityBoundaryCutoffParametrix.finite_cutoff_layer` of this split imports it.
-- source:
--   OpenAI, Global Uniqueness for the Smooth Isotropic Elasticity Inverse Problem, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 372; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Global-Uniqueness-for-the-Smooth-Isotropic-Elasticity-Inverse-Problem-September-24-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/Elasticity/BoundaryLayers.lean (declaration OAI.ElasticityBoundarySmoothOperator.scaledOperator_order_bound)

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
open Set MeasureTheory
open scoped BigOperators
namespace ElasticityBoundarySmoothOperator
open MvPolynomial ElasticityBoundaryMVCalculus ElasticityBoundaryMVNormal
  ElasticityBoundaryParameter ElasticityBoundaryParameterBounds ElasticityBoundaryTensorSeries
  ElasticityBoundaryActualTower ElasticityBoundaryTaylorPolynomial ElasticityBoundaryOrderBound
  ElasticityBoundaryScaling ElasticityBoundaryLayerOperator ElasticityBoundaryWeights

lemma scaledOperator_order_bound (a : SmoothTensor) (b : SmoothLower)
    (ha : ∀ i α j β, ContDiff ℝ (⊤ : ℕ∞) (a i α j β) ∧ HasCompactSupport (a i α j β))
    (hb : ∀ i j β, ContDiff ℝ (⊤ : ℕ∞) (b i j β) ∧ HasCompactSupport (b i j β))
    (q R : Polynomial W) (N : ℕ)
    (hR : operator (tensorTaylor a N) (lowerTaylor b N) q=Polynomial.X^(N+1)*R)
    (i : Fin 3) : OrderBound (fun δ y => scaledOperator a b q δ i y) (N+1) := by
  sorry

end ElasticityBoundarySmoothOperator

end
end

end OAI
end
