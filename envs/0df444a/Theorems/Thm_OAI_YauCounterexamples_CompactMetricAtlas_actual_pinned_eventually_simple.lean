-- Prove2me | Theorems.Thm_OAI_YauCounterexamples_CompactMetricAtlas_actual_pinned_eventually_simple
-- name    : OAI.YauCounterexamples.CompactMetricAtlas.actual_pinned_eventually_simple
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T11:52:18.123854+00:00
-- url     : https://prove2.me/theorems/e9fbe60f-70ba-4830-b2c9-88aeb9bc579b
-- title:
--   OAI.YauCounterexamples.CompactMetricAtlas.actual_pinned_eventually_simple: intermediate lemma from OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.YauCounterexamples.sphere_three` and `OAI.YauCounterexamples.sphere_two_torus_two`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth counterexamples to Yau's nodal upper bound in dimensions three and four*, OpenAI Math Release, September 23, 2026, result family 350, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.YauCounterexamples.CompactMetricAtlas.actual_pinned_eventually_simple` of [lean/OAI/Geometry/SmoothYau/Spectrum/VaryingSpectralResolventBase.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/Spectrum/VaryingSpectralResolventBase.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.YauCounterexamples.CompactMetricAtlas`, with `open Set Filter Function Manifold Bundle`, `open scoped Topology ContDiff BoundedContinuousFunction`):
--
--   ```lean
--   theorem actual_pinned_eventually_simple
--       (I : MetricIntegralAtlas (E := E) (M := M))
--       (B : ∀ i, A.PatchCoefficients i) (α : ℝ) (hα0 : 0 < α)
--       (hα : ∀ i, 1 ≤ α*(A.localInverse i).radius^2) (he : A.errorBound B α ≤ 1/2)
--       (lam : ℝ) (hn : α+lam ≠ 0)
--       (u : M → ℝ) (hu : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ u) (hu0 : u ≠ 0)
--       (hue : ∀ x, -laplaceBeltrami g u x = lam*u x)
--       {U : Set M} (K : pinningTensorSpace g u U)
--       (hnd : ∀ z : A.realH (2*(k:ℝ)),
--         A.realSpectralResolvent B α hα0 hα he z = (α+lam)⁻¹ • z →
--         I.mean g (fun x => u x*A.realValue (2*(k:ℝ)) z x) = 0 →
--         (∀ a : A.realH (2*(k:ℝ)),
--           A.realSpectralResolvent B α hα0 hα he a = (α+lam)⁻¹ • a →
--           I.mean g (fun x => u x*A.realValue (2*(k:ℝ)) a x) = 0 →
--           I.mean g (fun x => g.inner x (metricGradient g (A.realValue (2*(k:ℝ)) z) x)
--             (K.val x (metricGradient g (A.realValue (2*(k:ℝ)) a) x))) = 0) → z = 0) :
--       ∀ᶠ t in 𝓝[≠] (0:ℝ), ∀ v : M → ℝ,
--         ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ v →
--         (∀ x, -laplaceBeltrami (pinnedMetric g K.val K.property.1 t) v x = lam*v x) →
--         ∃ c : ℝ, v = fun x => c*u x
--   ```
--
--   **Definitions.** The statement is written with `OAI.YauCounterexamples.CompactMetricAtlas`, `OAI.YauCounterexamples.FourierSobolevSpace`, `OAI.YauCounterexamples.CompactMetricAtlas.H`, `OAI.YauCounterexamples.CompactMetricAtlas.PatchCoefficients` and `OAI.YauCounterexamples.LocalMetricInverse` (definitions bundle `OAIQ070A000` of this split); `OAI.YauCounterexamples.MetricIntegralAtlas` (definitions bundle `OAIQ070A001` of this split); `OAI.YauCounterexamples.metricGradient` (definitions bundle `OAIQ070A003` of this split); `OAI.YauCounterexamples.CompactMetricAtlas.errorBound`, `OAI.YauCounterexamples.CompactMetricAtlas.realH`, `OAI.YauCounterexamples.CompactMetricAtlas.realH_mod`, `OAI.YauCounterexamples.CompactMetricAtlas.realValue` and `OAI.YauCounterexamples.MetricIntegralAtlas.mean` (definitions bundle `OAIQ070A005` of this split); `OAI.YauCounterexamples.pinnedMetric` and `OAI.YauCounterexamples.pinningTensorSpace` (definitions bundle `OAIQ070A007` of this split); `OAI.YauCounterexamples.CompactMetricAtlas.realSpectralResolvent` (definitions bundle `OAIQ070A009` of this split); `OAI.YauCounterexamples.SmoothMetric` and `OAI.YauCounterexamples.laplaceBeltrami` (the published bundle `Def_SmoothYau`).
--
--   **Used by.** The proofs of `OAI.YauCounterexamples.exists_annular_simple_pinned_family` and `OAI.YauCounterexamples.exists_three_simple_pinned_family` of this split import it.
-- source:
--   OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 350; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Smooth-counterexamples-to-Yaus-nodal-upper-bound-in-dimensions-three-and-four-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/Spectrum/VaryingSpectralResolventBase.lean (declaration OAI.YauCounterexamples.CompactMetricAtlas.actual_pinned_eventually_simple)

import Mathlib
import Definitions.Def_SmoothYau
import Definitions.Def_OAIQ070A009

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

theorem actual_pinned_eventually_simple
    (I : MetricIntegralAtlas (E := E) (M := M))
    (B : ∀ i, A.PatchCoefficients i) (α : ℝ) (hα0 : 0 < α)
    (hα : ∀ i, 1 ≤ α*(A.localInverse i).radius^2) (he : A.errorBound B α ≤ 1/2)
    (lam : ℝ) (hn : α+lam ≠ 0)
    (u : M → ℝ) (hu : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ u) (hu0 : u ≠ 0)
    (hue : ∀ x, -laplaceBeltrami g u x = lam*u x)
    {U : Set M} (K : pinningTensorSpace g u U)
    (hnd : ∀ z : A.realH (2*(k:ℝ)),
      A.realSpectralResolvent B α hα0 hα he z = (α+lam)⁻¹ • z →
      I.mean g (fun x => u x*A.realValue (2*(k:ℝ)) z x) = 0 →
      (∀ a : A.realH (2*(k:ℝ)),
        A.realSpectralResolvent B α hα0 hα he a = (α+lam)⁻¹ • a →
        I.mean g (fun x => u x*A.realValue (2*(k:ℝ)) a x) = 0 →
        I.mean g (fun x => g.inner x (metricGradient g (A.realValue (2*(k:ℝ)) z) x)
          (K.val x (metricGradient g (A.realValue (2*(k:ℝ)) a) x))) = 0) → z = 0) :
    ∀ᶠ t in 𝓝[≠] (0:ℝ), ∀ v : M → ℝ,
      ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ v →
      (∀ x, -laplaceBeltrami (pinnedMetric g K.val K.property.1 t) v x = lam*v x) →
      ∃ c : ℝ, v = fun x => c*u x := by
  sorry
end CompactMetricAtlas

end YauCounterexamples
end

end OAI
end
