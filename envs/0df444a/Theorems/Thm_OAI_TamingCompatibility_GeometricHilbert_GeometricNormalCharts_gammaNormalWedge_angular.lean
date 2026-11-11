-- Prove2me | Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_GeometricNormalCharts_gammaNormalWedge_angular
-- name    : OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.gammaNormalWedge_angular
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T23:14:47.979688+00:00
-- url     : https://prove2.me/theorems/a6fb1d4f-9ee5-41a9-aa6f-589f28dbf568
-- title:
--   OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.gammaNormalWedge_angular: intermediate lemma from OpenAI, Taming implies compatibility on four-manifolds
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.TamingCompatibility.taming_implies_compatibility`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Taming implies compatibility on four-manifolds*, OpenAI Math Release, October 6, 2026, result family 342, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.gammaNormalWedge_angular` of [lean/OAI/Geometry/TamingCompatibility/Hodge/HodgeGlobalAngular.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/TamingCompatibility/Hodge/HodgeGlobalAngular.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts`, with `open Bundle ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart ManifoldVolume HodgeFrame Set`, `open scoped Manifold ContDiff Topology RealInnerProductSpace`):
--
--   ```lean
--   lemma gammaNormalWedge_angular (p : A.centers) :
--       ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) (r : ℝ), 0 < r → ∀ T : ℝ,
--         ∀ z ∈ (E p).normalCompact,
--         ∀ u v : MetricUnit (hermitianMetric J α hs ht),
--         (extChartAt Model p.val).symm (normalMap (E p).metricExtension (E p).frameExtension z.1 z.2) = u.val.proj →
--         (extChartAt Model p.val).symm z.1 = v.val.proj →
--         ∃ a b : UnitaryFrame.V, ‖a‖ = 1 ∧ ‖b‖ = 1 ∧
--         (1/2 : ℝ)*(coordinatePartition A p z.1*(E p).normalCutoff z.2*HodgeKernelBounds.leading r T ‖z.2‖)*
--           ‖UnitaryFrame.line a-normalGauge J α ht p.val (E p).chart (E p).metricExtension (E p).frameExtension z
--             (UnitaryFrame.line b)‖^2 -
--           (C*HodgeKernelBounds.leadingConstant (N+2))*(r⁻¹)^2/(1+‖z.2‖/r)^N ≤
--           unitFrameFunctional A J α ht E (hermitianMetric J α hs ht) u
--             (coordinateMatrix J α ht A E p (gammaPartitionLeading J α ht A E T r p)
--               (z.1,normalMap (E p).metricExtension (E p).frameExtension z.1 z.2)
--               (unitStarDirection A J α ht E (hermitianMetric J α hs ht) v))
--   ```
--
--   **Definitions.** The statement is written with `OAI.TamingCompatibility.UnitaryFrame.W` (definitions bundle `OAIQ239Tc001` of this split); `OAI.TamingCompatibility.MetricUnit`, `OAI.TamingCompatibility.HodgeNormalSymbol.W`, `OAI.TamingCompatibility.ManifoldLocalization.FiniteCharts` and `OAI.TamingCompatibility.UnitaryFrame.V` (definitions bundle `OAIQ239Tc003` of this split); `OAI.TamingCompatibility.GeometricHilbert.HodgeKernelBounds.leading` and `OAI.TamingCompatibility.GeometricHilbert.HodgeKernelBounds.leadingConstant` (definitions bundle `OAIQ239Tc004` of this split); `OAI.TamingCompatibility.ManifoldLocalization.coordinatePartition` and `OAI.TamingCompatibility.UnitaryFrame.line` (definitions bundle `OAIQ239Tc008` of this split); `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalGauge` and `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalMap` (definitions bundle `OAIQ239Tc014` of this split); `OAI.TamingCompatibility.hermitianMetric` (definitions bundle `OAIQ239Tc015` of this split); `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.FrameSpace` (definitions bundle `OAIQ239Tc017` of this split); `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.ParametrixData`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.coordinateMatrix`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.gammaPartitionLeading`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.unitFrameFunctional`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.unitStarDirection`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.ParametrixData.normalCompact`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.ParametrixData.normalCutoff` and `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.ParametrixData.source` (definitions bundle `OAIQ239Tc021` of this split); `OAI.TamingCompatibility.AlmostComplexStructure`, `OAI.TamingCompatibility.IsSmooth`, `OAI.TamingCompatibility.Model`, `OAI.TamingCompatibility.Space`, `OAI.TamingCompatibility.Tames` and `OAI.TamingCompatibility.TwoForm` (the published bundle `Def_TamingCompatibility`).
--
--   **Used by.** The proofs of `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.same_resolvent_angularNear_point`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.same_resolvent_positive_cross_lower` and `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.same_resolvent_wedge_mass_lower` of this split import it.
-- source:
--   OpenAI, Taming implies compatibility on four-manifolds, OpenAI Math Release, October 6, 2026, https://github.com/openai/math (result family 342; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Taming-implies-compatibility-on-four-manifolds-October-6-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/TamingCompatibility/Hodge/HodgeGlobalAngular.lean (declaration OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.gammaNormalWedge_angular)

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
lemma gammaNormalWedge_angular (p : A.centers) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) (r : ℝ), 0 < r → ∀ T : ℝ,
      ∀ z ∈ (E p).normalCompact,
      ∀ u v : MetricUnit (hermitianMetric J α hs ht),
      (extChartAt Model p.val).symm (normalMap (E p).metricExtension (E p).frameExtension z.1 z.2) = u.val.proj →
      (extChartAt Model p.val).symm z.1 = v.val.proj →
      ∃ a b : UnitaryFrame.V, ‖a‖ = 1 ∧ ‖b‖ = 1 ∧
      (1/2 : ℝ)*(coordinatePartition A p z.1*(E p).normalCutoff z.2*HodgeKernelBounds.leading r T ‖z.2‖)*
        ‖UnitaryFrame.line a-normalGauge J α ht p.val (E p).chart (E p).metricExtension (E p).frameExtension z
          (UnitaryFrame.line b)‖^2 -
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
