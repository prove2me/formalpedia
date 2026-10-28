-- Prove2me | Theorems.Thm_OAI_YauCounterexamples_CompactMetricAtlas_scalarTestCLM_pinned_deriv
-- name    : OAI.YauCounterexamples.CompactMetricAtlas.scalarTestCLM_pinned_deriv
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T11:54:01.428716+00:00
-- url     : https://prove2.me/theorems/f1c56e35-2e47-434e-9df2-4b6190f02687
-- title:
--   OAI.YauCounterexamples.CompactMetricAtlas.scalarTestCLM_pinned_deriv: intermediate lemma from OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.YauCounterexamples.sphere_three` and `OAI.YauCounterexamples.sphere_two_torus_two`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth counterexamples to Yau's nodal upper bound in dimensions three and four*, OpenAI Math Release, September 23, 2026, result family 350, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.YauCounterexamples.CompactMetricAtlas.scalarTestCLM_pinned_deriv` of [lean/OAI/Geometry/SmoothYau/Spectrum/VaryingSpectralResolventBase.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/Spectrum/VaryingSpectralResolventBase.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.YauCounterexamples.CompactMetricAtlas`, with `open Set Filter Function Manifold Bundle`, `open scoped Topology ContDiff BoundedContinuousFunction`):
--
--   ```lean
--   lemma scalarTestCLM_pinned_deriv (I : MetricIntegralAtlas (E := E) (M := M))
--       {u : M → ℝ} {U : Set M} (K : pinningTensorSpace g u U)
--       {a : M → ℝ} (ha : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ a)
--       (s : ℝ) (z : A.realH s) (hz : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ (A.realValue s z)) :
--       A.scalarTestCLM I s (laplaceDerivativeBCF (pinnedMetric g K.val K.property.1)
--         (fun p t _ hy i j => pinnedMetric_joint_coefficients g K.val K.property.1 p i j t hy) ha 0) z =
--         -I.mean g (fun x => g.inner x (metricGradient g (A.realValue s z) x)
--           (K.val x (metricGradient g a x)))
--   ```
--
--   **Definitions.** The statement is written with `OAI.YauCounterexamples.CompactMetricAtlas`, `OAI.YauCounterexamples.FourierSobolevSpace` and `OAI.YauCounterexamples.CompactMetricAtlas.H` (definitions bundle `OAIQ070A000` of this split); `OAI.YauCounterexamples.MetricIntegralAtlas` (definitions bundle `OAIQ070A001` of this split); `OAI.YauCounterexamples.metricGradient` (definitions bundle `OAIQ070A003` of this split); `OAI.YauCounterexamples.CompactMetricAtlas.realH`, `OAI.YauCounterexamples.CompactMetricAtlas.realH_acg`, `OAI.YauCounterexamples.CompactMetricAtlas.realH_mod`, `OAI.YauCounterexamples.CompactMetricAtlas.realValue`, `OAI.YauCounterexamples.CompactMetricAtlas.scalarTestCLM` and `OAI.YauCounterexamples.MetricIntegralAtlas.mean` (definitions bundle `OAIQ070A005` of this split); `OAI.YauCounterexamples.pinnedMetric`, `OAI.YauCounterexamples.pinnedMetric_joint_coefficients` and `OAI.YauCounterexamples.pinningTensorSpace` (definitions bundle `OAIQ070A007` of this split); `OAI.YauCounterexamples.laplaceDerivativeBCF` (definitions bundle `OAIQ070A010` of this split); `OAI.YauCounterexamples.CoordIndex` and `OAI.YauCounterexamples.SmoothMetric` (the published bundle `Def_SmoothYau`).
--
--   **Used by.** The proof of `OAI.YauCounterexamples.CompactMetricAtlas.actual_pinned_eventually_simple` of this split imports it.
-- source:
--   OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 350; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Smooth-counterexamples-to-Yaus-nodal-upper-bound-in-dimensions-three-and-four-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/Spectrum/VaryingSpectralResolventBase.lean (declaration OAI.YauCounterexamples.CompactMetricAtlas.scalarTestCLM_pinned_deriv)

import Mathlib
import Definitions.Def_SmoothYau
import Definitions.Def_OAIQ070A010

section

attribute [-instance] _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_finite _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_openPos _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples

open Set Filter Function Manifold Bundle
open scoped Topology ContDiff BoundedContinuousFunction
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [CompactSpace M] [T2Space M]
namespace CompactMetricAtlas
variable {g : SmoothMetric E M} {k : ℕ} {hs : Module.finrank ℝ E < 2*(2*(k:ℝ))}
variable (A : CompactMetricAtlas g k hs)

lemma scalarTestCLM_pinned_deriv (I : MetricIntegralAtlas (E := E) (M := M))
    {u : M → ℝ} {U : Set M} (K : pinningTensorSpace g u U)
    {a : M → ℝ} (ha : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ a)
    (s : ℝ) (z : A.realH s) (hz : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ (A.realValue s z)) :
    A.scalarTestCLM I s (laplaceDerivativeBCF (pinnedMetric g K.val K.property.1)
      (fun p t _ hy i j => pinnedMetric_joint_coefficients g K.val K.property.1 p i j t hy) ha 0) z =
      -I.mean g (fun x => g.inner x (metricGradient g (A.realValue s z) x)
        (K.val x (metricGradient g a x))) := by
  sorry

end CompactMetricAtlas

end YauCounterexamples
end

end OAI
end
