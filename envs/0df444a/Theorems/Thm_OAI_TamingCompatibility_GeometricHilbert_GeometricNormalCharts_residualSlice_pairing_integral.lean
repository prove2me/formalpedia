-- Prove2me | Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_GeometricNormalCharts_residualSlice_pairing_integral
-- name    : OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.residualSlice_pairing_integral
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T23:21:55.001045+00:00
-- url     : https://prove2.me/theorems/7fe801eb-e499-4ed8-b3ab-0a95c8371665
-- title:
--   OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.residualSlice_pairing_integral: intermediate lemma from OpenAI, Taming implies compatibility on four-manifolds
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.TamingCompatibility.taming_implies_compatibility`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Taming implies compatibility on four-manifolds*, OpenAI Math Release, October 6, 2026, result family 342, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.residualSlice_pairing_integral` of [lean/OAI/Geometry/TamingCompatibility/Hodge/HodgePatchPairing.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/TamingCompatibility/Hodge/HodgePatchPairing.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts`, with `open ManifoldForms ManifoldHodge ManifoldLocalization ManifoldVolume NormalJets NormalMetricCalculus CoordinateOperator`, `open HodgeNormalSymbol FirstJetGauge OrthogonalJets Filter Set OperatorCalculus UniformJets`, `open _root_.MeasureTheory`, `open scoped Manifold ContDiff Topology RealInnerProductSpace`):
--
--   ```lean
--   lemma residualSlice_pairing_integral (p : A.centers) {q : Space}
--       (hq : q ∈ Metric.closedBall (extChartAt Model p.val p.val) (E p).radius)
--       (t : ℝ) (u : W) (f : Space → W) :
--       (∫ y, chartDensity J α p.val y * ⟪f y,residualSlice J α ht A E p q t u y⟫) =
--       ∫ z, normalDensity (E p).metricExtension (E p).frameExtension (q,z) *
--         ⟪f (normalMap (E p).metricExtension (E p).frameExtension q z),
--           (E p).cutoffResidual J α ht q t (coordinatePartition A p q • u) z⟫
--   ```
--
--   **Definitions.** The statement is written with `OAI.TamingCompatibility.HodgeNormalSymbol.W`, `OAI.TamingCompatibility.ManifoldLocalization.FiniteCharts` and `OAI.TamingCompatibility.ManifoldVolume.chartDensity` (definitions bundle `OAIQ239Tc003` of this split); `OAI.TamingCompatibility.ManifoldLocalization.coordinatePartition` (definitions bundle `OAIQ239Tc008` of this split); `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalDensity` and `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalMap` (definitions bundle `OAIQ239Tc014` of this split); `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.ParametrixData`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.residualSlice` and `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.ParametrixData.cutoffResidual` (definitions bundle `OAIQ239Tc021` of this split); `OAI.TamingCompatibility.AlmostComplexStructure`, `OAI.TamingCompatibility.Model`, `OAI.TamingCompatibility.Space`, `OAI.TamingCompatibility.Tames` and `OAI.TamingCompatibility.TwoForm` (the published bundle `Def_TamingCompatibility`).
--
--   **Used by.** The proof of `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.leadingSlice_weak_deriv` of this split imports it.
-- source:
--   OpenAI, Taming implies compatibility on four-manifolds, OpenAI Math Release, October 6, 2026, https://github.com/openai/math (result family 342; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Taming-implies-compatibility-on-four-manifolds-October-6-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/TamingCompatibility/Hodge/HodgePatchPairing.lean (declaration OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.residualSlice_pairing_integral)

import Mathlib
import Definitions.Def_TamingCompatibility
import Definitions.Def_OAIQ239Tc021

section

attribute [-instance] _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge ManifoldLocalization ManifoldVolume NormalJets NormalMetricCalculus CoordinateOperator
open HodgeNormalSymbol FirstJetGauge OrthogonalJets Filter Set OperatorCalculus UniformJets
open _root_.MeasureTheory
open scoped Manifold ContDiff Topology RealInnerProductSpace
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace
attribute [local irreducible] normalGauge normalFirst pulledA pulledB normalDensity
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
  (A : FiniteCharts X) (E : ∀ p : A.centers, ParametrixData J α ht p.val)

local instance instNormedAddCommGroupMetricTensorSpace_12_rbc56ff_1 : NormedAddCommGroup (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedAddCommGroup
local instance instNormedSpaceRealMetricTensorSpace_12_rbc56ff_1 : NormedSpace ℝ (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedSpace
lemma residualSlice_pairing_integral (p : A.centers) {q : Space}
    (hq : q ∈ Metric.closedBall (extChartAt Model p.val p.val) (E p).radius)
    (t : ℝ) (u : W) (f : Space → W) :
    (∫ y, chartDensity J α p.val y * ⟪f y,residualSlice J α ht A E p q t u y⟫) =
    ∫ z, normalDensity (E p).metricExtension (E p).frameExtension (q,z) *
      ⟪f (normalMap (E p).metricExtension (E p).frameExtension q z),
        (E p).cutoffResidual J α ht q t (coordinatePartition A p q • u) z⟫ := by
  sorry

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
end
