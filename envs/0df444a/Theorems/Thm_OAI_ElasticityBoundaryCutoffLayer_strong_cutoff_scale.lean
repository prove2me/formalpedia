-- Prove2me | Theorems.Thm_OAI_ElasticityBoundaryCutoffLayer_strong_cutoff_scale
-- name    : OAI.ElasticityBoundaryCutoffLayer.strong_cutoff_scale
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T10:19:37.141487+00:00
-- url     : https://prove2.me/theorems/618bfe74-09b4-4d99-a80a-5fc01129f161
-- title:
--   OAI.ElasticityBoundaryCutoffLayer.strong_cutoff_scale: intermediate lemma from OpenAI, Global Uniqueness for the Smooth Isotropic Elasticity Inverse Problem
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Elasticity.global_uniqueness`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Global Uniqueness for the Smooth Isotropic Elasticity Inverse Problem*, OpenAI Math Release, September 24, 2026, result family 372, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ElasticityBoundaryCutoffLayer.strong_cutoff_scale` of [lean/OAI/MathematicalPhysics/Elasticity/BoundaryParametrix.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/Elasticity/BoundaryParametrix.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ElasticityBoundaryCutoffLayer`, with `open Set MeasureTheory Filter`, `open scoped BigOperators Topology`, `open MvPolynomial ElasticityBoundaryMVCalculus ElasticityBoundaryMVNormal`):
--
--   ```lean
--   theorem strong_cutoff_scale (a : SmoothTensor) (b : SmoothLower)
--       {χ : Y → ℂ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
--       {δ : ℝ} (hδ : δ≠0) (q : Polynomial W) (i : Fin 3) (y : Y) :
--       strong a b (cutoffLayer χ q δ) i (scale δ y) =
--         ((δ^4)⁻¹:ℝ) • (envelope δ y*cutoffScaled a b χ q δ i y)
--   ```
--
--   **Definitions.** The statement is written with `OAI.ElasticityBoundaryCutoffLayer.Y`, `OAI.ElasticityBoundaryCutoffLayer.cutoffLayer`, `OAI.ElasticityBoundaryCutoffLayer.cutoffScaled`, `OAI.ElasticityBoundaryMVCalculus.MP`, `OAI.ElasticityBoundaryMVNormal.W`, `OAI.ElasticityBoundaryProfile.envelope`, `OAI.ElasticityBoundaryScaling.Y`, `OAI.ElasticityBoundaryScaling.scale`, `OAI.ElasticityBoundarySmoothOperator.SmoothLower`, `OAI.ElasticityBoundarySmoothOperator.SmoothTensor` and `OAI.ElasticityBoundaryStrongLayer.strong` (definitions bundle `OAIQ6El001` of this split).
--
--   **Used by.** The proof of `OAI.ElasticityBoundaryCutoffParametrix.finite_cutoff_layer` of this split imports it.
-- source:
--   OpenAI, Global Uniqueness for the Smooth Isotropic Elasticity Inverse Problem, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 372; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Global-Uniqueness-for-the-Smooth-Isotropic-Elasticity-Inverse-Problem-September-24-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/Elasticity/BoundaryParametrix.lean (declaration OAI.ElasticityBoundaryCutoffLayer.strong_cutoff_scale)

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

theorem strong_cutoff_scale (a : SmoothTensor) (b : SmoothLower)
    {χ : Y → ℂ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    {δ : ℝ} (hδ : δ≠0) (q : Polynomial W) (i : Fin 3) (y : Y) :
    strong a b (cutoffLayer χ q δ) i (scale δ y) =
      ((δ^4)⁻¹:ℝ) • (envelope δ y*cutoffScaled a b χ q δ i y) := by
  sorry

end ElasticityBoundaryCutoffLayer

end
end

end OAI
end
