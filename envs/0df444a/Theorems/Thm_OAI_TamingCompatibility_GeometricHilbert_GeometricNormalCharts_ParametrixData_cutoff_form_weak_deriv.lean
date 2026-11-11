-- Prove2me | Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_GeometricNormalCharts_ParametrixData_cutoff_form_weak_deriv
-- name    : OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.ParametrixData.cutoff_form_weak_deriv
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T22:58:44.948815+00:00
-- url     : https://prove2.me/theorems/3e876b67-095a-4b42-8720-ec012c67621f
-- title:
--   OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.ParametrixData.cutoff_form_weak_deriv: intermediate lemma from OpenAI, Taming implies compatibility on four-manifolds
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.TamingCompatibility.taming_implies_compatibility`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Taming implies compatibility on four-manifolds*, OpenAI Math Release, October 6, 2026, result family 342, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.ParametrixData.cutoff_form_weak_deriv` of [lean/OAI/Geometry/TamingCompatibility/Hodge/HodgeParametrixFormWeak.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/TamingCompatibility/Hodge/HodgeParametrixFormWeak.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.ParametrixData`, with `open ManifoldForms ManifoldHodge NormalJets NormalMetricCalculus CoordinateOperator`, `open HodgeNormalSymbol FirstJetGauge OrthogonalJets Filter Set OperatorCalculus UniformJets`, `open _root_.MeasureTheory`, `open scoped Manifold ContDiff Topology RealInnerProductSpace`):
--
--   ```lean
--   lemma cutoff_form_weak_deriv (hs : IsSmooth α) {q : Space}
--       (hq : q ∈ Metric.closedBall (extChartAt Model p p) E.radius)
--       {t : ℝ} (htpos : 0 < t) (u : W) (a : TwoForm X) (ha : IsSmooth a) :
--       let g := E.metricExtension
--       let B := E.frameExtension
--       let D := E.chart
--       let χ : Space → ℝ := E.normalCutoff
--       let η := HodgeChart.rawVector J α ht p D a ∘ normalMap g B q
--       HasDerivAt (fun s => ∫ z, normalDensity g B (q,z) * ⟪η z,
--         normalGauge J α ht p D g B (q,z) (χ z • NormalHeatResidual.modelSection s u z)⟫)
--         ((∫ z, normalDensity g B (q,z) * ⟪η z,normalGauge J α ht p D g B (q,z)
--         (NormalHeatResidual.residual
--           (fun y => CutoffFamilies.principal (normalPrincipal g B) χ (q,y))
--           (fun y => CutoffFamilies.first (normalPrincipal g B) (gaugedFirst J α ht p D g B) χ (q,y))
--           (fun y => CutoffFamilies.zero (normalPrincipal g B) (gaugedFirst J α ht p D g B)
--             (gaugedZero J α ht p D g B) χ (q,y)) t z u)⟫) -
--       (∫ z, normalDensity g B (q,z) *
--         ⟪differential EuclideanEnergy.e (pulledA J α ht p D g B q) (pulledB J α ht p D g B q) η z,
--           differential EuclideanEnergy.e (pulledA J α ht p D g B q) (pulledB J α ht p D g B q)
--             (fun y => normalGauge J α ht p D g B (q,y) (χ y • NormalHeatResidual.modelSection t u y)) z⟫)) t
--   ```
--
--   **Definitions.** The statement is written with `OAI.TamingCompatibility.EuclideanEnergy.V` and `OAI.TamingCompatibility.EuclideanEnergy.e` (definitions bundle `OAIQ239Tc001` of this split); `OAI.TamingCompatibility.HodgeNormalSymbol.Q`, `OAI.TamingCompatibility.HodgeNormalSymbol.W`, `OAI.TamingCompatibility.GeometricHilbert.CutoffFamilies.first`, `OAI.TamingCompatibility.GeometricHilbert.CutoffFamilies.principal`, `OAI.TamingCompatibility.GeometricHilbert.CutoffFamilies.zero`, `OAI.TamingCompatibility.GeometricHilbert.FlatHeat.V`, `OAI.TamingCompatibility.GeometricHilbert.NormalHeatResidual.End`, `OAI.TamingCompatibility.GeometricHilbert.NormalHeatResidual.residual` and `OAI.TamingCompatibility.GeometricHilbert.NormalJets.MetricTensor` (definitions bundle `OAIQ239Tc003` of this split); `OAI.TamingCompatibility.GeometricHilbert.OperatorCalculus.differential` (definitions bundle `OAIQ239Tc004` of this split); `OAI.TamingCompatibility.GeometricHilbert.NormalHeatResidual.modelSection` (definitions bundle `OAIQ239Tc008` of this split); `OAI.TamingCompatibility.GeometricChart.Data` (definitions bundle `OAIQ239Tc011` of this split); `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.gaugedFirst`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.gaugedZero`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalDensity`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalGauge`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalMap`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalPrincipal`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.pulledA` and `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.pulledB` (definitions bundle `OAIQ239Tc014` of this split); `OAI.TamingCompatibility.HodgeChart.rawVector` (definitions bundle `OAIQ239Tc018` of this split); `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.ParametrixData` and `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.ParametrixData.normalCutoff` (definitions bundle `OAIQ239Tc021` of this split); `OAI.TamingCompatibility.AlmostComplexStructure`, `OAI.TamingCompatibility.IsSmooth`, `OAI.TamingCompatibility.Model`, `OAI.TamingCompatibility.Space`, `OAI.TamingCompatibility.Tames` and `OAI.TamingCompatibility.TwoForm` (the published bundle `Def_TamingCompatibility`).
--
--   **Used by.** The proof of `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.leadingSlice_weak_deriv` of this split imports it.
-- source:
--   OpenAI, Taming implies compatibility on four-manifolds, OpenAI Math Release, October 6, 2026, https://github.com/openai/math (result family 342; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Taming-implies-compatibility-on-four-manifolds-October-6-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/TamingCompatibility/Hodge/HodgeParametrixFormWeak.lean (declaration OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.ParametrixData.cutoff_form_weak_deriv)

import Mathlib
import Definitions.Def_TamingCompatibility
import Definitions.Def_OAIQ239Tc021

section

attribute [-instance] _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge NormalJets NormalMetricCalculus CoordinateOperator
open HodgeNormalSymbol FirstJetGauge OrthogonalJets Filter Set OperatorCalculus UniformJets
open _root_.MeasureTheory
open scoped Manifold ContDiff Topology RealInnerProductSpace
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
namespace ParametrixData
variable {J : AlmostComplexStructure X} {α : TwoForm X} {ht : Tames α J} {p : X}
  (E : ParametrixData J α ht p)

local instance instNormedAddCommGroupMetricTensorSpace_8_rf12fd7_1 : NormedAddCommGroup (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedAddCommGroup
local instance instNormedSpaceRealMetricTensorSpace_8_rf12fd7_1 : NormedSpace ℝ (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedSpace
lemma cutoff_form_weak_deriv (hs : IsSmooth α) {q : Space}
    (hq : q ∈ Metric.closedBall (extChartAt Model p p) E.radius)
    {t : ℝ} (htpos : 0 < t) (u : W) (a : TwoForm X) (ha : IsSmooth a) :
    let g := E.metricExtension
    let B := E.frameExtension
    let D := E.chart
    let χ : Space → ℝ := E.normalCutoff
    let η := HodgeChart.rawVector J α ht p D a ∘ normalMap g B q
    HasDerivAt (fun s => ∫ z, normalDensity g B (q,z) * ⟪η z,
      normalGauge J α ht p D g B (q,z) (χ z • NormalHeatResidual.modelSection s u z)⟫)
      ((∫ z, normalDensity g B (q,z) * ⟪η z,normalGauge J α ht p D g B (q,z)
      (NormalHeatResidual.residual
        (fun y => CutoffFamilies.principal (normalPrincipal g B) χ (q,y))
        (fun y => CutoffFamilies.first (normalPrincipal g B) (gaugedFirst J α ht p D g B) χ (q,y))
        (fun y => CutoffFamilies.zero (normalPrincipal g B) (gaugedFirst J α ht p D g B)
          (gaugedZero J α ht p D g B) χ (q,y)) t z u)⟫) -
    (∫ z, normalDensity g B (q,z) *
      ⟪differential EuclideanEnergy.e (pulledA J α ht p D g B q) (pulledB J α ht p D g B q) η z,
        differential EuclideanEnergy.e (pulledA J α ht p D g B q) (pulledB J α ht p D g B q)
          (fun y => normalGauge J α ht p D g B (q,y) (χ y • NormalHeatResidual.modelSection t u y)) z⟫)) t := by
  sorry

end ParametrixData
end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
end
