-- Prove2me | Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_GeometricNormalCharts_gammaNormalWedge_actual_angular
-- name    : OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.gammaNormalWedge_actual_angular
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T23:11:58.927302+00:00
-- url     : https://prove2.me/theorems/f3ac464a-ebc5-41b8-baf0-ee1b820739a0
-- title:
--   OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.gammaNormalWedge_actual_angular: intermediate lemma from OpenAI, Taming implies compatibility on four-manifolds
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.TamingCompatibility.taming_implies_compatibility`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Taming implies compatibility on four-manifolds*, OpenAI Math Release, October 6, 2026, result family 342, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.gammaNormalWedge_actual_angular` of [lean/OAI/Geometry/TamingCompatibility/Hodge/HodgeActualAngular.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/TamingCompatibility/Hodge/HodgeActualAngular.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts`, with `open Bundle ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart ManifoldVolume HodgeFrame Set`, `open scoped Manifold ContDiff Topology RealInnerProductSpace`):
--
--   ```lean
--   lemma gammaNormalWedge_actual_angular (p : A.centers) :
--       ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) (r : ℝ), 0 < r → ∀ T : ℝ,
--         ∀ z ∈ (E p).normalCompact,
--         ∀ u v : MetricUnit (hermitianMetric J α hs ht),
--         (extChartAt Model p.val).symm (normalMap (E p).metricExtension (E p).frameExtension z.1 z.2) = u.val.proj →
--         (extChartAt Model p.val).symm z.1 = v.val.proj →
--         (1/2 : ℝ)*(coordinatePartition A p z.1*(E p).normalCutoff z.2*HodgeKernelBounds.leading r T ‖z.2‖)*
--           (normalAngular A J α hs ht E p z u v)^2 -
--           (C*HodgeKernelBounds.leadingConstant (N+2))*(r⁻¹)^2/(1+‖z.2‖/r)^N ≤
--           unitFrameFunctional A J α ht E (hermitianMetric J α hs ht) u
--             (coordinateMatrix J α ht A E p (gammaPartitionLeading J α ht A E T r p)
--               (z.1,normalMap (E p).metricExtension (E p).frameExtension z.1 z.2)
--               (unitStarDirection A J α ht E (hermitianMetric J α hs ht) v))
--   ```
--
--   **Definitions.** The statement is written with `OAI.TamingCompatibility.MetricUnit` and `OAI.TamingCompatibility.ManifoldLocalization.FiniteCharts` (definitions bundle `OAIQ239Tc003` of this split); `OAI.TamingCompatibility.GeometricHilbert.HodgeKernelBounds.leading` and `OAI.TamingCompatibility.GeometricHilbert.HodgeKernelBounds.leadingConstant` (definitions bundle `OAIQ239Tc004` of this split); `OAI.TamingCompatibility.ManifoldLocalization.coordinatePartition` (definitions bundle `OAIQ239Tc008` of this split); `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalMap` (definitions bundle `OAIQ239Tc014` of this split); `OAI.TamingCompatibility.hermitianMetric` (definitions bundle `OAIQ239Tc015` of this split); `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.FrameSpace` (definitions bundle `OAIQ239Tc017` of this split); `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.ParametrixData`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.coordinateMatrix`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.gammaPartitionLeading`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalAngular`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.unitFrameFunctional`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.unitStarDirection`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.ParametrixData.normalCompact`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.ParametrixData.normalCutoff` and `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.ParametrixData.source` (definitions bundle `OAIQ239Tc021` of this split); `OAI.TamingCompatibility.AlmostComplexStructure`, `OAI.TamingCompatibility.IsSmooth`, `OAI.TamingCompatibility.Model`, `OAI.TamingCompatibility.Space`, `OAI.TamingCompatibility.Tames` and `OAI.TamingCompatibility.TwoForm` (the published bundle `Def_TamingCompatibility`).
--
--   **Used by.** The proof of `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.same_resolvent_angularNear_point` of this split imports it.
-- source:
--   OpenAI, Taming implies compatibility on four-manifolds, OpenAI Math Release, October 6, 2026, https://github.com/openai/math (result family 342; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Taming-implies-compatibility-on-four-manifolds-October-6-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/TamingCompatibility/Hodge/HodgeActualAngular.lean (declaration OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.gammaNormalWedge_actual_angular)

import Mathlib
import Definitions.Def_TamingCompatibility
import Definitions.Def_OAIQ239Tc021

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart ManifoldVolume HodgeFrame Set
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [T2Space X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)

include hE in
lemma gammaNormalWedge_actual_angular (p : A.centers) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) (r : ℝ), 0 < r → ∀ T : ℝ,
      ∀ z ∈ (E p).normalCompact,
      ∀ u v : MetricUnit (hermitianMetric J α hs ht),
      (extChartAt Model p.val).symm (normalMap (E p).metricExtension (E p).frameExtension z.1 z.2) = u.val.proj →
      (extChartAt Model p.val).symm z.1 = v.val.proj →
      (1/2 : ℝ)*(coordinatePartition A p z.1*(E p).normalCutoff z.2*HodgeKernelBounds.leading r T ‖z.2‖)*
        (normalAngular A J α hs ht E p z u v)^2 -
        (C*HodgeKernelBounds.leadingConstant (N+2))*(r⁻¹)^2/(1+‖z.2‖/r)^N ≤
        unitFrameFunctional A J α ht E (hermitianMetric J α hs ht) u
          (coordinateMatrix J α ht A E p (gammaPartitionLeading J α ht A E T r p)
            (z.1,normalMap (E p).metricExtension (E p).frameExtension z.1 z.2)
            (unitStarDirection A J α ht E (hermitianMetric J α hs ht) v)) := by
  sorry

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end OAI
end
