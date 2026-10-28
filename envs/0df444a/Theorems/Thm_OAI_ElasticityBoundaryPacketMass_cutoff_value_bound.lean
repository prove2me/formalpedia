-- Prove2me | Theorems.Thm_OAI_ElasticityBoundaryPacketMass_cutoff_value_bound
-- name    : OAI.ElasticityBoundaryPacketMass.cutoff_value_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T10:28:32.627601+00:00
-- url     : https://prove2.me/theorems/77e8e482-af24-4138-b0bd-8500579f9533
-- title:
--   OAI.ElasticityBoundaryPacketMass.cutoff_value_bound: intermediate lemma from OpenAI, Global Uniqueness for the Smooth Isotropic Elasticity Inverse Problem
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Elasticity.global_uniqueness`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Global Uniqueness for the Smooth Isotropic Elasticity Inverse Problem*, OpenAI Math Release, September 24, 2026, result family 372, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ElasticityBoundaryPacketMass.cutoff_value_bound` of [lean/OAI/MathematicalPhysics/Elasticity/BoundaryPackets.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/Elasticity/BoundaryPackets.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ElasticityBoundaryPacketMass`, with `open Set MeasureTheory`, `open scoped BigOperators`, `open ElasticityBoundaryCutoffParametrix ElasticityBoundaryCutoffLayer`):
--
--   ```lean
--   lemma cutoff_value_bound {χ : Y → ℂ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
--       (hc : HasCompactSupport χ) (q : Polynomial W) (j : I) :
--       ∃ C : ℝ, 0≤C ∧ ∀ δ : ℝ, 0<δ → δ≤1 →
--         MemLp (cutoffLayer χ q δ j) 2 (volume.restrict halfspace) ∧
--         (∫ z in halfspace, ‖cutoffLayer χ q δ j z‖^2)≤C*δ^4
--   ```
--
--   **Definitions.** The statement is written with `OAI.ElasticityBoundaryCutoffLayer.Y`, `OAI.ElasticityBoundaryCutoffLayer.cutoffLayer`, `OAI.ElasticityBoundaryMVCalculus.MP`, `OAI.ElasticityBoundaryMVNormal.W`, `OAI.ElasticityBoundaryPacketMass.I`, `OAI.ElasticityBoundaryPacketMass.Y`, `OAI.ElasticityBoundaryProfileBounds.Y` and `OAI.ElasticityBoundaryProfileBounds.halfspace` (definitions bundle `OAIQ6El001` of this split).
--
--   **Used by.** The proof of `OAI.ElasticityBoundaryPacket.Setup.trial_size` of this split imports it.
-- source:
--   OpenAI, Global Uniqueness for the Smooth Isotropic Elasticity Inverse Problem, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 372; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Global-Uniqueness-for-the-Smooth-Isotropic-Elasticity-Inverse-Problem-September-24-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/Elasticity/BoundaryPackets.lean (declaration OAI.ElasticityBoundaryPacketMass.cutoff_value_bound)

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
open Set MeasureTheory
open scoped BigOperators
namespace ElasticityBoundaryPacketMass
open ElasticityBoundaryCutoffParametrix ElasticityBoundaryCutoffLayer
  ElasticityBoundaryProfile ElasticityBoundaryParameter ElasticityBoundaryParameterBounds
  ElasticityBoundaryOrderBound ElasticityBoundaryCutoffBound ElasticityBoundaryScaling
  ElasticityBoundaryWeights ElasticityBoundaryStrongLayer ElasticityBoundaryMVCalculus
  ElasticityBoundaryTensorSeries ElasticityBoundaryProfileBounds ElasticityBoundaryMVNormal ElasticityBoundaryActualTower

lemma cutoff_value_bound {χ : Y → ℂ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hc : HasCompactSupport χ) (q : Polynomial W) (j : I) :
    ∃ C : ℝ, 0≤C ∧ ∀ δ : ℝ, 0<δ → δ≤1 →
      MemLp (cutoffLayer χ q δ j) 2 (volume.restrict halfspace) ∧
      (∫ z in halfspace, ‖cutoffLayer χ q δ j z‖^2)≤C*δ^4 := by
  sorry

end ElasticityBoundaryPacketMass

end
end

end OAI
end
