-- Prove2me | Theorems.Thm_OAI_ElasticityBoundaryCutoffLayer_correction_order_bound
-- name    : OAI.ElasticityBoundaryCutoffLayer.correction_order_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T10:19:10.451429+00:00
-- url     : https://prove2.me/theorems/4ef84a42-fd24-4fe4-8aa6-53cdd295afe4
-- title:
--   OAI.ElasticityBoundaryCutoffLayer.correction_order_bound: intermediate lemma from OpenAI, Global Uniqueness for the Smooth Isotropic Elasticity Inverse Problem
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Elasticity.global_uniqueness`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Global Uniqueness for the Smooth Isotropic Elasticity Inverse Problem*, OpenAI Math Release, September 24, 2026, result family 372, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ElasticityBoundaryCutoffLayer.correction_order_bound` of [lean/OAI/MathematicalPhysics/Elasticity/BoundaryParametrix.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/Elasticity/BoundaryParametrix.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ElasticityBoundaryCutoffLayer`, with `open Set MeasureTheory Filter`, `open scoped BigOperators Topology`, `open MvPolynomial ElasticityBoundaryMVCalculus ElasticityBoundaryMVNormal`):
--
--   ```lean
--   lemma correction_order_bound (a : SmoothTensor) (b : SmoothLower)
--       (ha : ∀ i α j β, Continuous (a i α j β) ∧ HasCompactSupport (a i α j β))
--       (hb : ∀ i j β, Continuous (b i j β) ∧ HasCompactSupport (b i j β))
--       {χ : Y → ℂ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hc : HasCompactSupport χ)
--       (hχ0 : χ =ᶠ[𝓝 (0:Y)] fun _ => 1) (q : Polynomial W) (N : ℕ) (i : Fin 3) :
--       OrderBound (fun δ y => cutoffCorrection a b χ q δ i y) N
--   ```
--
--   **Definitions.** The statement is written with `OAI.ElasticityBoundaryCutoffLayer.Y`, `OAI.ElasticityBoundaryCutoffLayer.cutoffCorrection`, `OAI.ElasticityBoundaryMVCalculus.MP`, `OAI.ElasticityBoundaryMVNormal.W`, `OAI.ElasticityBoundaryOrderBound.OrderBound`, `OAI.ElasticityBoundaryOrderBound.Y`, `OAI.ElasticityBoundarySmoothOperator.SmoothLower`, `OAI.ElasticityBoundarySmoothOperator.SmoothTensor` and `OAI.ElasticityBoundarySmoothOperator.Y` (definitions bundle `OAIQ6El001` of this split).
--
--   **Used by.** The proof of `OAI.ElasticityBoundaryCutoffParametrix.finite_cutoff_layer` of this split imports it.
-- source:
--   OpenAI, Global Uniqueness for the Smooth Isotropic Elasticity Inverse Problem, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 372; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Global-Uniqueness-for-the-Smooth-Isotropic-Elasticity-Inverse-Problem-September-24-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/Elasticity/BoundaryParametrix.lean (declaration OAI.ElasticityBoundaryCutoffLayer.correction_order_bound)

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
namespace ElasticityBoundaryCutoffLayer
open MvPolynomial ElasticityBoundaryMVCalculus ElasticityBoundaryMVNormal
  ElasticityBoundaryParameter ElasticityBoundaryParameterBounds ElasticityBoundaryTensorSeries
  ElasticityBoundaryActualTower ElasticityBoundarySmoothOperator ElasticityBoundaryProfile
  ElasticityBoundaryProfileBounds ElasticityBoundaryScaling ElasticityBoundaryLayerOperator
  ElasticityBoundaryWeights ElasticityBoundaryStrongLayer ElasticityBoundaryOrderBound
  ElasticityBoundaryCutoffBound

lemma correction_order_bound (a : SmoothTensor) (b : SmoothLower)
    (ha : ∀ i α j β, Continuous (a i α j β) ∧ HasCompactSupport (a i α j β))
    (hb : ∀ i j β, Continuous (b i j β) ∧ HasCompactSupport (b i j β))
    {χ : Y → ℂ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hc : HasCompactSupport χ)
    (hχ0 : χ =ᶠ[𝓝 (0:Y)] fun _ => 1) (q : Polynomial W) (N : ℕ) (i : Fin 3) :
    OrderBound (fun δ y => cutoffCorrection a b χ q δ i y) N := by
  sorry

end ElasticityBoundaryCutoffLayer

end
end

end OAI
end
