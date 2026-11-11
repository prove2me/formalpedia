-- Prove2me | Theorems.Thm_OAI_TamingCompatibility_separating_probability_local_quadratic
-- name    : OAI.TamingCompatibility.separating_probability_local_quadratic
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T22:57:43.426204+00:00
-- url     : https://prove2.me/theorems/93bebfa1-8838-4817-8788-b34a9cf2f2bc
-- title:
--   OAI.TamingCompatibility.separating_probability_local_quadratic: intermediate lemma from OpenAI, Taming implies compatibility on four-manifolds
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.TamingCompatibility.taming_implies_compatibility`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Taming implies compatibility on four-manifolds*, OpenAI Math Release, October 6, 2026, result family 342, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.TamingCompatibility.separating_probability_local_quadratic` of [lean/OAI/Geometry/TamingCompatibility/Charts/GeometricLocalMass.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/TamingCompatibility/Charts/GeometricLocalMass.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.TamingCompatibility`, with `open ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart ManifoldVolume`, `open GeometricHilbert Set _root_.MeasureTheory`, `open scoped Manifold ContDiff SchwartzMap`):
--
--   ```lean
--   theorem separating_probability_local_quadratic
--       (J : AlmostComplexStructure X) (α : TwoForm X) (hs : IsSmooth α) (ht : Tames α J)
--       (μ : Measure (MetricUnit (hermitianMetric J α hs ht))) [IsProbabilityMeasure μ]
--       (hann : ∀ β : smoothForms X 2, IsClosed β.val → IsInvariant β.val J →
--         unitMeasureCurrent J (hermitianMetric J α hs ht) μ β = 0) (x : X) :
--       ∃ p : X, ∃ R C r : ℝ, x ∈ (extChartAt Model p).source ∧
--         0 < R ∧ 0 ≤ C ∧ 0 < r ∧ r ≤ 2*R ∧
--         Metric.closedBall (extChartAt Model p x) (4*R) ⊆ (extChartAt Model p).target ∧
--         ∀ s ∈ Ioc (0:ℝ) r, ∀ b ∈ Metric.closedBall (extChartAt Model p x) R,
--           μ.real {u : MetricUnit (hermitianMetric J α hs ht) |
--             u.val.proj ∈ (extChartAt Model p).symm '' Metric.closedBall b s} ≤ C*s^2
--   ```
--
--   **Definitions.** The statement is written with `OAI.TamingCompatibility.ManifoldForms.Form`, `OAI.TamingCompatibility.ManifoldForms.Model` and `OAI.TamingCompatibility.ManifoldForms.Space` (definitions bundle `OAIQ239Tc002` of this split); `OAI.TamingCompatibility.MetricUnit` and `OAI.TamingCompatibility.unitMeasurable` (definitions bundle `OAIQ239Tc003` of this split); `OAI.TamingCompatibility.ManifoldForms.smoothForms` (definitions bundle `OAIQ239Tc011` of this split); `OAI.TamingCompatibility.hermitianMetric` (definitions bundle `OAIQ239Tc015` of this split); `OAI.TamingCompatibility.unitMeasureCurrent` (definitions bundle `OAIQ239Tc020` of this split); `OAI.TamingCompatibility.AlmostComplexStructure`, `OAI.TamingCompatibility.IsClosed`, `OAI.TamingCompatibility.IsInvariant`, `OAI.TamingCompatibility.IsSmooth`, `OAI.TamingCompatibility.Model`, `OAI.TamingCompatibility.Space`, `OAI.TamingCompatibility.Tames` and `OAI.TamingCompatibility.TwoForm` (the published bundle `Def_TamingCompatibility`).
--
--   **Used by.** The proofs of `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.concentration_double_physical_tail`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.concentration_forces_correction_zero`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.physicalGradientMass_L2_limit`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.separating_current_angular_moment`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.separating_current_euclidean_angular_profile`, `OAI.TamingCompatibility.GeometricHilbert.Hermitian.separating_probability_transverse_product_limit`, `OAI.TamingCompatibility.GeometricHilbert.separating_current_L2_correction` and `OAI.TamingCompatibility.GeometricHilbert.separating_current_wedge_upper` of this split import it.
-- source:
--   OpenAI, Taming implies compatibility on four-manifolds, OpenAI Math Release, October 6, 2026, https://github.com/openai/math (result family 342; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Taming-implies-compatibility-on-four-manifolds-October-6-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/TamingCompatibility/Charts/GeometricLocalMass.lean (declaration OAI.TamingCompatibility.separating_probability_local_quadratic)

import Mathlib
import Definitions.Def_TamingCompatibility
import Definitions.Def_OAIQ239Tc020

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

section
noncomputable section
namespace TamingCompatibility
open ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart ManifoldVolume
open GeometricHilbert Set _root_.MeasureTheory
open scoped Manifold ContDiff SchwartzMap
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] unitMeasurable unitBorel

theorem separating_probability_local_quadratic
    (J : AlmostComplexStructure X) (α : TwoForm X) (hs : IsSmooth α) (ht : Tames α J)
    (μ : Measure (MetricUnit (hermitianMetric J α hs ht))) [IsProbabilityMeasure μ]
    (hann : ∀ β : smoothForms X 2, IsClosed β.val → IsInvariant β.val J →
      unitMeasureCurrent J (hermitianMetric J α hs ht) μ β = 0) (x : X) :
    ∃ p : X, ∃ R C r : ℝ, x ∈ (extChartAt Model p).source ∧
      0 < R ∧ 0 ≤ C ∧ 0 < r ∧ r ≤ 2*R ∧
      Metric.closedBall (extChartAt Model p x) (4*R) ⊆ (extChartAt Model p).target ∧
      ∀ s ∈ Ioc (0:ℝ) r, ∀ b ∈ Metric.closedBall (extChartAt Model p x) R,
        μ.real {u : MetricUnit (hermitianMetric J α hs ht) |
          u.val.proj ∈ (extChartAt Model p).symm '' Metric.closedBall b s} ≤ C*s^2 := by
  sorry
end TamingCompatibility

end
end

end
end

end OAI
end
