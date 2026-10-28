-- Prove2me | Theorems.Thm_OAI_YauCounterexamples_CompactMetricAtlas_global_cutoff_raw_controls
-- name    : OAI.YauCounterexamples.CompactMetricAtlas.global_cutoff_raw_controls
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T11:21:05.350549+00:00
-- url     : https://prove2.me/theorems/d1b494cb-2717-4a50-b693-058b42add5a9
-- title:
--   OAI.YauCounterexamples.CompactMetricAtlas.global_cutoff_raw_controls: intermediate lemma from OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.YauCounterexamples.sphere_three` and `OAI.YauCounterexamples.sphere_two_torus_two`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth counterexamples to Yau's nodal upper bound in dimensions three and four*, OpenAI Math Release, September 23, 2026, result family 350, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.YauCounterexamples.CompactMetricAtlas.global_cutoff_raw_controls` of [lean/OAI/Geometry/SmoothYau/Limits/CutoffFactorCompactRaw.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/Limits/CutoffFactorCompactRaw.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.YauCounterexamples.CompactMetricAtlas`, with `open Set Filter Function Manifold`, `open scoped Topology ContDiff`):
--
--   ```lean
--   theorem global_cutoff_raw_controls (i₀ : CoordIndex E) (χ : M → ℝ)
--       (hχ : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ χ) :
--       ∃ C > 0, ∀ (b v : M → ℝ),
--         ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ b → ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ v →
--         ∀ ε : ℝ, 0 ≤ ε → ε ≤ 1 →
--         (∀ t ∈ A.coveringRawTests i₀, ∀ y ∈ t.compactSet, ∀ j ≤ 1,
--           ‖iteratedFDeriv ℝ j ((fun x => b x-1) ∘ (chartAt E t.center).symm) y‖ ≤ ε) →
--         (∀ t ∈ A.coveringRawTests i₀, ∀ y ∈ t.compactSet, ∀ j ≤ 2,
--           ‖iteratedFDeriv ℝ j ((fun x => v x-1) ∘ (chartAt E t.center).symm) y‖ ≤ ε) →
--         ∀ x : M,
--           |weightedLaplacian g b (cutoffFactor χ v) x| ≤ C*ε ∧
--           Real.sqrt (coordinateGradientPair g (cutoffFactor χ v) (cutoffFactor χ v) x) ≤ C*ε
--   ```
--
--   **Definitions.** The statement is written with `OAI.YauCounterexamples.CompactMetricAtlas` and `OAI.YauCounterexamples.CompactMetricAtlas.coveringRawTests` (definitions bundle `OAIQ070A000` of this split); `OAI.YauCounterexamples.coordinateGradientPair`, `OAI.YauCounterexamples.cutoffFactor` and `OAI.YauCounterexamples.weightedLaplacian` (definitions bundle `OAIQ070A004` of this split); `OAI.YauCounterexamples.CoordIndex`, `OAI.YauCounterexamples.CoordinateTest` and `OAI.YauCounterexamples.SmoothMetric` (the published bundle `Def_SmoothYau`).
--
--   **Used by.** The proofs of `OAI.YauCounterexamples.exists_spherical_exact_stage` and `OAI.YauCounterexamples.exists_three_exact_stage` of this split import it.
-- source:
--   OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 350; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Smooth-counterexamples-to-Yaus-nodal-upper-bound-in-dimensions-three-and-four-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/Limits/CutoffFactorCompactRaw.lean (declaration OAI.YauCounterexamples.CompactMetricAtlas.global_cutoff_raw_controls)

import Mathlib
import Definitions.Def_SmoothYau
import Definitions.Def_OAIQ070A000
import Definitions.Def_OAIQ070A004

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples

open Set Filter Function Manifold
open scoped Topology ContDiff
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [T2Space M] [CompactSpace M]

namespace CompactMetricAtlas
variable {g : SmoothMetric E M} {k : ℕ} {hs : Module.finrank ℝ E < 2*(2*(k:ℝ))}
  (A : CompactMetricAtlas g k hs)

omit [T2Space M] in
theorem global_cutoff_raw_controls (i₀ : CoordIndex E) (χ : M → ℝ)
    (hχ : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ χ) :
    ∃ C > 0, ∀ (b v : M → ℝ),
      ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ b → ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ v →
      ∀ ε : ℝ, 0 ≤ ε → ε ≤ 1 →
      (∀ t ∈ A.coveringRawTests i₀, ∀ y ∈ t.compactSet, ∀ j ≤ 1,
        ‖iteratedFDeriv ℝ j ((fun x => b x-1) ∘ (chartAt E t.center).symm) y‖ ≤ ε) →
      (∀ t ∈ A.coveringRawTests i₀, ∀ y ∈ t.compactSet, ∀ j ≤ 2,
        ‖iteratedFDeriv ℝ j ((fun x => v x-1) ∘ (chartAt E t.center).symm) y‖ ≤ ε) →
      ∀ x : M,
        |weightedLaplacian g b (cutoffFactor χ v) x| ≤ C*ε ∧
        Real.sqrt (coordinateGradientPair g (cutoffFactor χ v) (cutoffFactor χ v) x) ≤ C*ε := by
  sorry
end CompactMetricAtlas

end YauCounterexamples
end

end OAI
end
