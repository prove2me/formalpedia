-- Prove2me | Theorems.Thm_OAI_TamingCompatibility_separating_probability_atlas_defect
-- name    : OAI.TamingCompatibility.separating_probability_atlas_defect
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T23:26:28.282592+00:00
-- url     : https://prove2.me/theorems/c53a09cb-f724-49c2-a457-f7528ea2a385
-- title:
--   OAI.TamingCompatibility.separating_probability_atlas_defect: intermediate lemma from OpenAI, Taming implies compatibility on four-manifolds
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.TamingCompatibility.taming_implies_compatibility`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Taming implies compatibility on four-manifolds*, OpenAI Math Release, October 6, 2026, result family 342, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.TamingCompatibility.separating_probability_atlas_defect` of [lean/OAI/Geometry/TamingCompatibility/Charts/RadialAtlasProducer.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/TamingCompatibility/Charts/RadialAtlasProducer.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.TamingCompatibility`, with `open Bundle ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart ManifoldVolume`, `open GeometricHilbert GeometricHilbert.Hermitian Set _root_.MeasureTheory`, `open scoped Manifold ContDiff SchwartzMap`):
--
--   ```lean
--   theorem separating_probability_atlas_defect
--       (J : AlmostComplexStructure X) (α : TwoForm X) (hs : IsSmooth α) (ht : Tames α J)
--       (A : FiniteCharts X) (D : ∀ p : A.centers, Data J α ht p.val)
--       (hA : ∀ p, tsupport (A.partition p) ⊆ (D p).source)
--       (μ : Measure (MetricUnit (hermitianMetric J α hs ht))) [IsProbabilityMeasure μ]
--       (hann : ∀ β : smoothForms X 2, IsClosed β.val → IsInvariant β.val J →
--         unitMeasureCurrent J (hermitianMetric J α hs ht) μ β = 0)
--       (p : A.centers) (x : X) (hp : A.partition p x ≠ 0) :
--       ∃ r : ℝ, 0 < r ∧
--         Metric.closedBall (extChartAt Model p.val x) r ⊆ (extChartAt Model p.val).target ∧
--         Integrable (smoothUnitDefect J α hs ht p.val (extChartAt Model p.val x) r 0) μ
--   ```
--
--   **Definitions.** The statement is written with `OAI.TamingCompatibility.ManifoldForms.Form`, `OAI.TamingCompatibility.ManifoldForms.Model` and `OAI.TamingCompatibility.ManifoldForms.Space` (definitions bundle `OAIQ239Tc002` of this split); `OAI.TamingCompatibility.MetricUnit`, `OAI.TamingCompatibility.unitMeasurable` and `OAI.TamingCompatibility.ManifoldLocalization.FiniteCharts` (definitions bundle `OAIQ239Tc003` of this split); `OAI.TamingCompatibility.GeometricChart.Data`, `OAI.TamingCompatibility.ManifoldForms.smoothForms` and `OAI.TamingCompatibility.GeometricChart.Data.source` (definitions bundle `OAIQ239Tc011` of this split); `OAI.TamingCompatibility.hermitianMetric` (definitions bundle `OAIQ239Tc015` of this split); `OAI.TamingCompatibility.unitMeasureCurrent` (definitions bundle `OAIQ239Tc020` of this split); `OAI.TamingCompatibility.GeometricHilbert.Hermitian.smoothUnitDefect` (definitions bundle `OAIQ239Tc022` of this split); `OAI.TamingCompatibility.AlmostComplexStructure`, `OAI.TamingCompatibility.IsClosed`, `OAI.TamingCompatibility.IsInvariant`, `OAI.TamingCompatibility.IsSmooth`, `OAI.TamingCompatibility.Model`, `OAI.TamingCompatibility.Space`, `OAI.TamingCompatibility.Tames` and `OAI.TamingCompatibility.TwoForm` (the published bundle `Def_TamingCompatibility`).
--
--   **Used by.** The proof of `OAI.TamingCompatibility.GeometricHilbert.Hermitian.separating_probability_transverse_product_limit` of this split imports it.
-- source:
--   OpenAI, Taming implies compatibility on four-manifolds, OpenAI Math Release, October 6, 2026, https://github.com/openai/math (result family 342; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Taming-implies-compatibility-on-four-manifolds-October-6-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/TamingCompatibility/Charts/RadialAtlasProducer.lean (declaration OAI.TamingCompatibility.separating_probability_atlas_defect)

import Mathlib
import Definitions.Def_TamingCompatibility
import Definitions.Def_OAIQ239Tc022

section

attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace TamingCompatibility
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart ManifoldVolume
open GeometricHilbert GeometricHilbert.Hermitian Set _root_.MeasureTheory
open scoped Manifold ContDiff SchwartzMap
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
attribute [local instance] unitMeasurable unitBorel

theorem separating_probability_atlas_defect
    (J : AlmostComplexStructure X) (α : TwoForm X) (hs : IsSmooth α) (ht : Tames α J)
    (A : FiniteCharts X) (D : ∀ p : A.centers, Data J α ht p.val)
    (hA : ∀ p, tsupport (A.partition p) ⊆ (D p).source)
    (μ : Measure (MetricUnit (hermitianMetric J α hs ht))) [IsProbabilityMeasure μ]
    (hann : ∀ β : smoothForms X 2, IsClosed β.val → IsInvariant β.val J →
      unitMeasureCurrent J (hermitianMetric J α hs ht) μ β = 0)
    (p : A.centers) (x : X) (hp : A.partition p x ≠ 0) :
    ∃ r : ℝ, 0 < r ∧
      Metric.closedBall (extChartAt Model p.val x) r ⊆ (extChartAt Model p.val).target ∧
      Integrable (smoothUnitDefect J α hs ht p.val (extChartAt Model p.val x) r 0) μ := by
  sorry
end TamingCompatibility

end
end

end OAI
end
