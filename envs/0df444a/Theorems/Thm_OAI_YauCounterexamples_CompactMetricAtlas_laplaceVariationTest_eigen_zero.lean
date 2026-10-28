-- Prove2me | Theorems.Thm_OAI_YauCounterexamples_CompactMetricAtlas_laplaceVariationTest_eigen_zero
-- name    : OAI.YauCounterexamples.CompactMetricAtlas.laplaceVariationTest_eigen_zero
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T11:33:24.368738+00:00
-- url     : https://prove2.me/theorems/82446bfc-4028-4d32-8be8-d63d6ebb6b31
-- title:
--   OAI.YauCounterexamples.CompactMetricAtlas.laplaceVariationTest_eigen_zero: intermediate lemma from OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.YauCounterexamples.sphere_three` and `OAI.YauCounterexamples.sphere_two_torus_two`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth counterexamples to Yau's nodal upper bound in dimensions three and four*, OpenAI Math Release, September 23, 2026, result family 350, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.YauCounterexamples.CompactMetricAtlas.laplaceVariationTest_eigen_zero` of [lean/OAI/Geometry/SmoothYau/Spectrum/VaryingSpectralResolventBase.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/Spectrum/VaryingSpectralResolventBase.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.YauCounterexamples.CompactMetricAtlas`, with `open Set Filter Function Manifold Bundle`, `open scoped Topology ContDiff BoundedContinuousFunction`):
--
--   ```lean
--   lemma laplaceVariationTest_eigen_zero (s t : ℝ)
--       (hbase : q 0 = g) (hm : ∀ f, I.mean (q t) f = I.mean g f)
--       (z : A.realH s) (hz : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ (A.realValue s z))
--       (lam : ℝ) (hea : ∀ x, -laplaceBeltrami g a x = lam*a x)
--       (hez : ∀ x, -laplaceBeltrami (q t) (A.realValue s z) x = lam*A.realValue s z x) :
--       A.laplaceVariationTest q hq ha I s t z = 0
--   ```
--
--   **Definitions.** The statement is written with `OAI.YauCounterexamples.CompactMetricAtlas`, `OAI.YauCounterexamples.FourierSobolevSpace` and `OAI.YauCounterexamples.CompactMetricAtlas.H` (definitions bundle `OAIQ070A000` of this split); `OAI.YauCounterexamples.MetricIntegralAtlas` (definitions bundle `OAIQ070A001` of this split); `OAI.YauCounterexamples.CompactMetricAtlas.laplaceVariationTest`, `OAI.YauCounterexamples.CompactMetricAtlas.realH`, `OAI.YauCounterexamples.CompactMetricAtlas.realH_mod`, `OAI.YauCounterexamples.CompactMetricAtlas.realValue` and `OAI.YauCounterexamples.MetricIntegralAtlas.mean` (definitions bundle `OAIQ070A005` of this split); `OAI.YauCounterexamples.CoordIndex`, `OAI.YauCounterexamples.SmoothMetric`, `OAI.YauCounterexamples.laplaceBeltrami` and `OAI.YauCounterexamples.metricCoefficients` (the published bundle `Def_SmoothYau`).
--
--   **Used by.** The proof of `OAI.YauCounterexamples.CompactMetricAtlas.actual_pinned_eventually_simple` of this split imports it.
-- source:
--   OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 350; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Smooth-counterexamples-to-Yaus-nodal-upper-bound-in-dimensions-three-and-four-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/Spectrum/VaryingSpectralResolventBase.lean (declaration OAI.YauCounterexamples.CompactMetricAtlas.laplaceVariationTest_eigen_zero)

import Mathlib
import Definitions.Def_SmoothYau
import Definitions.Def_OAIQ070A005

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples

section
open Set Filter Function Manifold Bundle
open scoped Topology ContDiff BoundedContinuousFunction
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [CompactSpace M] [T2Space M]

variable (q : ℝ → SmoothMetric E M)
variable (hq : ∀ p t y, y ∈ (chartAt E p).target → ∀ i j,
  ContDiffAt ℝ ∞ (fun z : ℝ × E => metricCoefficients (q z.1) p z.2 i j) (t,y))
variable {a : M → ℝ} (ha : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ a)

namespace CompactMetricAtlas
variable {g : SmoothMetric E M} {k : ℕ} {hs : Module.finrank ℝ E < 2*(2*(k:ℝ))}
variable (A : CompactMetricAtlas g k hs) (I : MetricIntegralAtlas (E := E) (M := M))

omit [T2Space M] in
lemma laplaceVariationTest_eigen_zero (s t : ℝ)
    (hbase : q 0 = g) (hm : ∀ f, I.mean (q t) f = I.mean g f)
    (z : A.realH s) (hz : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ (A.realValue s z))
    (lam : ℝ) (hea : ∀ x, -laplaceBeltrami g a x = lam*a x)
    (hez : ∀ x, -laplaceBeltrami (q t) (A.realValue s z) x = lam*A.realValue s z x) :
    A.laplaceVariationTest q hq ha I s t z = 0 := by
  sorry
end CompactMetricAtlas
end

open Set Filter Function Manifold Bundle
open scoped Topology ContDiff BoundedContinuousFunction

end YauCounterexamples
end

end OAI
end
