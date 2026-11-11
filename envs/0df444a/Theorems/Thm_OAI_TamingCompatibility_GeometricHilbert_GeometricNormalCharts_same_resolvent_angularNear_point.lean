-- Prove2me | Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_GeometricNormalCharts_same_resolvent_angularNear_point
-- name    : OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.same_resolvent_angularNear_point
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T23:23:31.250048+00:00
-- url     : https://prove2.me/theorems/5c8ed727-63a6-4b8b-855c-2d2ec593b437
-- title:
--   OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.same_resolvent_angularNear_point: intermediate lemma from OpenAI, Taming implies compatibility on four-manifolds
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.TamingCompatibility.taming_implies_compatibility`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Taming implies compatibility on four-manifolds*, OpenAI Math Release, October 6, 2026, result family 342, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.same_resolvent_angularNear_point` of [lean/OAI/Geometry/TamingCompatibility/Hodge/HodgeWedgeMassUpper.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/TamingCompatibility/Hodge/HodgeWedgeMassUpper.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts`, with `open Bundle ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart HodgeFrame Set _root_.MeasureTheory`, `open scoped Manifold ContDiff Topology RealInnerProductSpace ENNReal`):
--
--   ```lean
--   lemma same_resolvent_angularNear_point :
--       let := geometricMetricSpace J α hs ht
--       ∃ T c C B : ℝ, 0 < T ∧ 0 < c ∧ 0 ≤ C ∧ 0 ≤ B ∧
--         ∀ (r : ℝ) (hr : 0 < r), 2*r^2 ≤ T →
--         ∀ S : HodgeSmoothingCover A J α hs ht D hD r hr,
--         ∀ p : A.centers, ∀ uv : UnitPair J α hs ht,
--           c*(r⁻¹)^4*angularNear A J α hs ht E r p uv ≤
--             S.wedgeKernel (hermitianMetric J α hs ht) uv.1 uv.2 +
--               (C/r^2)*((1+dist uv.1.val.proj uv.2.val.proj/r)⁻¹)^6+B
--   ```
--
--   **Definitions.** The statement is written with `OAI.TamingCompatibility.MetricUnit` and `OAI.TamingCompatibility.ManifoldLocalization.FiniteCharts` (definitions bundle `OAIQ239Tc003` of this split); `OAI.TamingCompatibility.GeometricChart.Data.source` (definitions bundle `OAIQ239Tc011` of this split); `OAI.TamingCompatibility.hermitianMetric` and `OAI.TamingCompatibility.HodgeChart.Data` (definitions bundle `OAIQ239Tc015` of this split); `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.geometricMetricSpace` (definitions bundle `OAIQ239Tc018` of this split); `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.ParametrixData`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.UnitPair`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.angularNear` and `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.ParametrixData.source` (definitions bundle `OAIQ239Tc021` of this split); `OAI.TamingCompatibility.GeometricHilbert.HodgeSmoothingCover` and `OAI.TamingCompatibility.GeometricHilbert.HodgeSmoothingCover.wedgeKernel` (definitions bundle `OAIQ239Tc022` of this split); `OAI.TamingCompatibility.AlmostComplexStructure`, `OAI.TamingCompatibility.IsSmooth`, `OAI.TamingCompatibility.Model`, `OAI.TamingCompatibility.Space`, `OAI.TamingCompatibility.Tames` and `OAI.TamingCompatibility.TwoForm` (the published bundle `Def_TamingCompatibility`).
--
--   **Used by.** The proof of `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.separating_current_angular_moment` of this split imports it.
-- source:
--   OpenAI, Taming implies compatibility on four-manifolds, OpenAI Math Release, October 6, 2026, https://github.com/openai/math (result family 342; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Taming-implies-compatibility-on-four-manifolds-October-6-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/TamingCompatibility/Hodge/HodgeWedgeMassUpper.lean (declaration OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.same_resolvent_angularNear_point)

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
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart HodgeFrame Set _root_.MeasureTheory
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
lemma same_resolvent_angularNear_point :
    let := geometricMetricSpace J α hs ht
    ∃ T c C B : ℝ, 0 < T ∧ 0 < c ∧ 0 ≤ C ∧ 0 ≤ B ∧
      ∀ (r : ℝ) (hr : 0 < r), 2*r^2 ≤ T →
      ∀ S : HodgeSmoothingCover A J α hs ht D hD r hr,
      ∀ p : A.centers, ∀ uv : UnitPair J α hs ht,
        c*(r⁻¹)^4*angularNear A J α hs ht E r p uv ≤
          S.wedgeKernel (hermitianMetric J α hs ht) uv.1 uv.2 +
            (C/r^2)*((1+dist uv.1.val.proj uv.2.val.proj/r)⁻¹)^6+B := by
  sorry

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end OAI
end
