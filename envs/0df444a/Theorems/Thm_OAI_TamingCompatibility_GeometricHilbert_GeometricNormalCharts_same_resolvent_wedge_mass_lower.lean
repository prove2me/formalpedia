-- Prove2me | Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_GeometricNormalCharts_same_resolvent_wedge_mass_lower
-- name    : OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.same_resolvent_wedge_mass_lower
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T23:23:40.764086+00:00
-- url     : https://prove2.me/theorems/c8edde69-b004-46b2-ab81-ba43ee2f1000
-- title:
--   OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.same_resolvent_wedge_mass_lower: intermediate lemma from OpenAI, Taming implies compatibility on four-manifolds
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.TamingCompatibility.taming_implies_compatibility`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Taming implies compatibility on four-manifolds*, OpenAI Math Release, October 6, 2026, result family 342, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.same_resolvent_wedge_mass_lower` of [lean/OAI/Geometry/TamingCompatibility/Hodge/HodgeWedgeMassLower.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/TamingCompatibility/Hodge/HodgeWedgeMassLower.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts`, with `open Bundle ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart ManifoldVolume HodgeFrame Set _root_.MeasureTheory`, `open scoped Manifold ContDiff Topology RealInnerProductSpace ENNReal`):
--
--   ```lean
--   lemma same_resolvent_wedge_mass_lower :
--       let := geometricMetricSpace J α hs ht
--       ∃ C B : ℝ, 0 ≤ C ∧ 0 ≤ B ∧
--         ∀ (μ : Measure (MetricUnit (hermitianMetric J α hs ht))) [IsProbabilityMeasure μ],
--         ∀ M : ℝ, 0 ≤ M →
--         (∀ x : X, ∀ s : ℝ, 0 < s →
--           μ.real {v | ENNReal.ofReal (dist x v.val.proj) < ENNReal.ofReal s} ≤ M*s^2) →
--         ∀ (r : ℝ) (hr : 0 < r),
--         ∀ S : HodgeSmoothingCover A J α hs ht D hD r hr,
--           -(C*M+B) ≤ ⟪S.regularize (hermitianMetric J α hs ht) μ,
--             l2Star A J α hs ht (S.regularize (hermitianMetric J α hs ht) μ)⟫
--   ```
--
--   **Definitions.** The statement is written with `OAI.TamingCompatibility.MetricUnit`, `OAI.TamingCompatibility.unitMeasurable` and `OAI.TamingCompatibility.ManifoldLocalization.FiniteCharts` (definitions bundle `OAIQ239Tc003` of this split); `OAI.TamingCompatibility.GeometricChart.Data.source` (definitions bundle `OAIQ239Tc011` of this split); `OAI.TamingCompatibility.GeometricHilbert.L2`, `OAI.TamingCompatibility.GeometricHilbert.PreL2`, `OAI.TamingCompatibility.GeometricHilbert.l2Star`, `OAI.TamingCompatibility.GeometricHilbert.preL2Add`, `OAI.TamingCompatibility.GeometricHilbert.preL2Inner`, `OAI.TamingCompatibility.GeometricHilbert.preL2Module` and `OAI.TamingCompatibility.GeometricHilbert.preL2Normed` (definitions bundle `OAIQ239Tc014` of this split); `OAI.TamingCompatibility.hermitianMetric` and `OAI.TamingCompatibility.HodgeChart.Data` (definitions bundle `OAIQ239Tc015` of this split); `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.geometricMetricSpace` (definitions bundle `OAIQ239Tc018` of this split); `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.ParametrixData` and `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.ParametrixData.source` (definitions bundle `OAIQ239Tc021` of this split); `OAI.TamingCompatibility.GeometricHilbert.HodgeSmoothingCover` and `OAI.TamingCompatibility.GeometricHilbert.HodgeSmoothingCover.regularize` (definitions bundle `OAIQ239Tc022` of this split); `OAI.TamingCompatibility.AlmostComplexStructure`, `OAI.TamingCompatibility.IsSmooth`, `OAI.TamingCompatibility.Model`, `OAI.TamingCompatibility.Space`, `OAI.TamingCompatibility.Tames` and `OAI.TamingCompatibility.TwoForm` (the published bundle `Def_TamingCompatibility`).
--
--   **Used by.** The proof of `OAI.TamingCompatibility.GeometricHilbert.separating_current_L2_correction` of this split imports it.
-- source:
--   OpenAI, Taming implies compatibility on four-manifolds, OpenAI Math Release, October 6, 2026, https://github.com/openai/math (result family 342; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Taming-implies-compatibility-on-four-manifolds-October-6-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/TamingCompatibility/Hodge/HodgeWedgeMassLower.lean (declaration OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.same_resolvent_wedge_mass_lower)

import Mathlib
import Definitions.Def_TamingCompatibility
import Definitions.Def_OAIQ239Tc021
import Definitions.Def_OAIQ239Tc022

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart ManifoldVolume HodgeFrame Set _root_.MeasureTheory
open scoped Manifold ContDiff Topology RealInnerProductSpace ENNReal
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [T2Space X] [ConnectedSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)
  (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
  (hD : ∀ p, tsupport (A.partition p) ⊆ (D p).source)
attribute [local instance] unitMeasurable unitBorel

include hE in
lemma same_resolvent_wedge_mass_lower :
    let := geometricMetricSpace J α hs ht
    ∃ C B : ℝ, 0 ≤ C ∧ 0 ≤ B ∧
      ∀ (μ : Measure (MetricUnit (hermitianMetric J α hs ht))) [IsProbabilityMeasure μ],
      ∀ M : ℝ, 0 ≤ M →
      (∀ x : X, ∀ s : ℝ, 0 < s →
        μ.real {v | ENNReal.ofReal (dist x v.val.proj) < ENNReal.ofReal s} ≤ M*s^2) →
      ∀ (r : ℝ) (hr : 0 < r),
      ∀ S : HodgeSmoothingCover A J α hs ht D hD r hr,
        -(C*M+B) ≤ ⟪S.regularize (hermitianMetric J α hs ht) μ,
          l2Star A J α hs ht (S.regularize (hermitianMetric J α hs ht) μ)⟫ := by
  sorry

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end OAI
end
