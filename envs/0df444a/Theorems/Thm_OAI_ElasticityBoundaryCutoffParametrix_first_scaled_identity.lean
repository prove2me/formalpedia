-- Prove2me | Theorems.Thm_OAI_ElasticityBoundaryCutoffParametrix_first_scaled_identity
-- name    : OAI.ElasticityBoundaryCutoffParametrix.first_scaled_identity
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T10:19:57.498676+00:00
-- url     : https://prove2.me/theorems/a50994e1-1cf5-42fd-8686-8e8804944e50
-- title:
--   OAI.ElasticityBoundaryCutoffParametrix.first_scaled_identity: intermediate lemma from OpenAI, Global Uniqueness for the Smooth Isotropic Elasticity Inverse Problem
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Elasticity.global_uniqueness`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Global Uniqueness for the Smooth Isotropic Elasticity Inverse Problem*, OpenAI Math Release, September 24, 2026, result family 372, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ElasticityBoundaryCutoffParametrix.first_scaled_identity` of [lean/OAI/MathematicalPhysics/Elasticity/BoundaryParametrix.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/Elasticity/BoundaryParametrix.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ElasticityBoundaryCutoffParametrix`, with `open Set MeasureTheory Filter`, `open scoped BigOperators Topology`, `open MvPolynomial ElasticityBoundaryMVCalculus ElasticityBoundaryMVNormal`):
--
--   ```lean
--   lemma first_scaled_identity {χ : Y → ℂ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
--       {δ : ℝ} (hδ : δ≠0) (q : Polynomial W) (j β : Fin 3) (y : Y) :
--       dpart (cutoffLayer χ q δ j) β (scale δ y)=
--         ((δ^2)⁻¹:ℝ) • (envelope δ y*firstScaled χ q δ j β y)
--   ```
--
--   **Definitions.** The statement is written with `OAI.ElasticityBoundaryCutoffLayer.cutoffLayer`, `OAI.ElasticityBoundaryCutoffParametrix.Y`, `OAI.ElasticityBoundaryCutoffParametrix.firstScaled`, `OAI.ElasticityBoundaryMVCalculus.MP`, `OAI.ElasticityBoundaryMVNormal.W`, `OAI.ElasticityBoundaryProfile.envelope`, `OAI.ElasticityBoundaryScaling.Y`, `OAI.ElasticityBoundaryScaling.scale` and `OAI.ElasticityBoundaryStrongLayer.dpart` (definitions bundle `OAIQ6El001` of this split).
--
--   **Used by.** The proofs of `OAI.ElasticityBoundaryMixedScaling.mixedEnergy_limit` and `OAI.ElasticityBoundaryPacket.Setup.field_gradient_mass` of this split import it.
-- source:
--   OpenAI, Global Uniqueness for the Smooth Isotropic Elasticity Inverse Problem, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 372; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Global-Uniqueness-for-the-Smooth-Isotropic-Elasticity-Inverse-Problem-September-24-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/Elasticity/BoundaryParametrix.lean (declaration OAI.ElasticityBoundaryCutoffParametrix.first_scaled_identity)

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

lemma first_scaled_identity {χ : Y → ℂ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    {δ : ℝ} (hδ : δ≠0) (q : Polynomial W) (j β : Fin 3) (y : Y) :
    dpart (cutoffLayer χ q δ j) β (scale δ y)=
      ((δ^2)⁻¹:ℝ) • (envelope δ y*firstScaled χ q δ j β y) := by
  sorry

end ElasticityBoundaryCutoffParametrix

end
end

end OAI
end
