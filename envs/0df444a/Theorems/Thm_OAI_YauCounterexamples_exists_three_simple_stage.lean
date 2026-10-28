-- Prove2me | Theorems.Thm_OAI_YauCounterexamples_exists_three_simple_stage
-- name    : OAI.YauCounterexamples.exists_three_simple_stage
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T12:08:22.249077+00:00
-- url     : https://prove2.me/theorems/20d6ea24-b235-435c-bf18-cd4e01a2447d
-- title:
--   OAI.YauCounterexamples.exists_three_simple_stage: intermediate lemma from OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.YauCounterexamples.sphere_three` and `OAI.YauCounterexamples.sphere_two_torus_two`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth counterexamples to Yau's nodal upper bound in dimensions three and four*, OpenAI Math Release, September 23, 2026, result family 350, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.YauCounterexamples.exists_three_simple_stage` of [lean/OAI/Geometry/SmoothYau/SphereMetric/ThreeFixedFormNorm.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/SphereMetric/ThreeFixedFormNorm.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.YauCounterexamples`, with `open Set Filter Function Manifold Bundle TopologicalSpace BoxIntegral Metric`, `open scoped Topology ContDiff Distributions ENNReal NNReal`):
--
--   ```lean
--   theorem exists_three_simple_stage :
--       ∃ R : ℝ, 0<R ∧ ∃ N : Set (SmoothMetric ThreeModel ThreeManifold),
--         IsSmoothNeighborhood threeBackgroundMetric N ∧ threeBackgroundMetric∈N ∧
--         ∀ g∈N, ∀ r : ℝ, 0 < r → ∀ hrR : r<R/2, (hext : ThreeExterior g r) →
--         ∀ A : ℝ, 0 ≤ A → ∀ M : ℕ, ∀ U : Set (ThreeTensor R), IsOpen U →
--         threeTensorOf R g (hext.mono hrR.le)∈U →
--         ∃ k : ℕ, M ≤ k ∧ 3 ≤ k ∧ ∃ h : SmoothMetric ThreeModel ThreeManifold,
--         ∃ c : ℝ, 0 < c ∧ ∃ hcR : c<R/2, ∃ he : ThreeExterior h c,
--         threeTensorOf R h (he.mono hcR.le)∈U ∧
--         ∃ u : ThreeManifold → ℝ, ContMDiff 𝓘(ℝ,ThreeModel) 𝓘(ℝ,ℝ) ∞ u ∧ u≠0 ∧
--           (∀ q, -laplaceBeltrami h u q=productFrequency k*u q) ∧
--           ThreeRegular u ∧ ThreeSimple h u (productFrequency k) ∧ ThreeSignAbove R u (A*(k:ℝ))
--   ```
--
--   **Definitions.** The statement is written with `OAI.YauCounterexamples.MetricForm` (definitions bundle `OAIQ070A002` of this split); `OAI.YauCounterexamples.ThreeManifold`, `OAI.YauCounterexamples.ThreeModel`, `OAI.YauCounterexamples.ThreeProductModel`, `OAI.YauCounterexamples.ThreeRegular`, `OAI.YauCounterexamples.threeChartedSpace` and `OAI.YauCounterexamples.threeIsManifold` (definitions bundle `OAIQ070A003` of this split); `OAI.YauCounterexamples.productFrequency` (definitions bundle `OAIQ070A004` of this split); `OAI.YauCounterexamples.ThreeExterior`, `OAI.YauCounterexamples.ThreeSignAbove`, `OAI.YauCounterexamples.ThreeSimple`, `OAI.YauCounterexamples.ThreeTensor`, `OAI.YauCounterexamples.threeAmbientFormNorm`, `OAI.YauCounterexamples.threeAmbientFormSpace`, `OAI.YauCounterexamples.threeBackgroundMetric`, `OAI.YauCounterexamples.threeTensorSupport` and `OAI.YauCounterexamples.ThreeExterior.mono` (definitions bundle `OAIQ070A006` of this split); `OAI.YauCounterexamples.threeTensorOf` (definitions bundle `OAIQ070A010` of this split); `OAI.YauCounterexamples.Euclidean`, `OAI.YauCounterexamples.IsSmoothNeighborhood`, `OAI.YauCounterexamples.SmoothMetric`, `OAI.YauCounterexamples.Sphere` and `OAI.YauCounterexamples.laplaceBeltrami` (the published bundle `Def_SmoothYau`).
--
--   **Used by.** The proof of `OAI.YauCounterexamples.exists_three_fixed_witnesses` of this split imports it.
-- source:
--   OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 350; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Smooth-counterexamples-to-Yaus-nodal-upper-bound-in-dimensions-three-and-four-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/SphereMetric/ThreeFixedFormNorm.lean (declaration OAI.YauCounterexamples.exists_three_simple_stage)

import Mathlib
import Definitions.Def_SmoothYau
import Definitions.Def_OAIQ070A010

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples

section
open Set Filter Function Manifold Bundle TopologicalSpace BoxIntegral Metric
open scoped Topology ContDiff Distributions ENNReal NNReal

local instance threeStageFormNorm_r0d5085_1 : NormedAddCommGroup (MetricForm ThreeModel) := inferInstanceAs (NormedAddCommGroup (ThreeModel →L[ℝ] ThreeModel →L[ℝ] ℝ))
local instance threeStageFormSpace_r0d5085_1 : NormedSpace ℝ (MetricForm ThreeModel) := inferInstanceAs (NormedSpace ℝ (ThreeModel →L[ℝ] ThreeModel →L[ℝ] ℝ))
theorem exists_three_simple_stage :
    ∃ R : ℝ, 0<R ∧ ∃ N : Set (SmoothMetric ThreeModel ThreeManifold),
      IsSmoothNeighborhood threeBackgroundMetric N ∧ threeBackgroundMetric∈N ∧
      ∀ g∈N, ∀ r : ℝ, 0 < r → ∀ hrR : r<R/2, (hext : ThreeExterior g r) →
      ∀ A : ℝ, 0 ≤ A → ∀ M : ℕ, ∀ U : Set (ThreeTensor R), IsOpen U →
      threeTensorOf R g (hext.mono hrR.le)∈U →
      ∃ k : ℕ, M ≤ k ∧ 3 ≤ k ∧ ∃ h : SmoothMetric ThreeModel ThreeManifold,
      ∃ c : ℝ, 0 < c ∧ ∃ hcR : c<R/2, ∃ he : ThreeExterior h c,
      threeTensorOf R h (he.mono hcR.le)∈U ∧
      ∃ u : ThreeManifold → ℝ, ContMDiff 𝓘(ℝ,ThreeModel) 𝓘(ℝ,ℝ) ∞ u ∧ u≠0 ∧
        (∀ q, -laplaceBeltrami h u q=productFrequency k*u q) ∧
        ThreeRegular u ∧ ThreeSimple h u (productFrequency k) ∧ ThreeSignAbove R u (A*(k:ℝ)) := by
  sorry
end

open Set Filter Function Manifold Bundle TopologicalSpace BoxIntegral
open scoped Topology ContDiff Distributions ENNReal NNReal

end YauCounterexamples
end

end OAI
end
