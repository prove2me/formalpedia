-- Prove2me | Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_GeometricNormalCharts_actual_cutoff_square_eq
-- name    : OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.actual_cutoff_square_eq
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T23:14:27.679475+00:00
-- url     : https://prove2.me/theorems/c6c04134-ede5-4b23-9e37-14c463d5b493
-- title:
--   OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.actual_cutoff_square_eq: intermediate lemma from OpenAI, Taming implies compatibility on four-manifolds
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.TamingCompatibility.taming_implies_compatibility`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Taming implies compatibility on four-manifolds*, OpenAI Math Release, October 6, 2026, result family 342, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.actual_cutoff_square_eq` of [lean/OAI/Geometry/TamingCompatibility/Concentration/HodgeParametrixResidual.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/TamingCompatibility/Concentration/HodgeParametrixResidual.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts`, with `open ManifoldForms ManifoldHodge NormalJets NormalMetricCalculus CoordinateOperator`, `open HodgeNormalSymbol FirstJetGauge OrthogonalJets Filter Set OperatorCalculus UniformJets`, `open scoped Manifold ContDiff Topology RealInnerProductSpace`):
--
--   ```lean
--   lemma actual_cutoff_square_eq (hs : IsSmooth α) (hg : ContDiff ℝ ∞ g) (hB : ContDiff ℝ ∞ B)
--       (hsym : ∀ y v w, g y v w = g y w v) {q z : Space}
--       (hactual : ActualData J α ht p D q g B)
--       (hz : (q,z) ∈ normalDomain J α ht p D g B)
--       (hgact : g (normalMap g B q z) = (coordinateMetric J α ht p (normalMap g B q z)).bilinear)
--       (χ : Space → ℝ) (hχ : ContDiff ℝ ∞ χ) {t : ℝ} (htpos : 0 < t) (u : W) :
--         deriv (fun s => normalGauge J α ht p D g B (q,z) (χ z • NormalHeatResidual.modelSection s u z)) t +
--           weightedAdjoint EuclideanEnergy.e (pulledA J α ht p D g B q)
--             (pulledB J α ht p D g B q) (fun y => normalDensity g B (q,y))
--             (differential EuclideanEnergy.e (pulledA J α ht p D g B q)
--               (pulledB J α ht p D g B q)
--               (fun y => normalGauge J α ht p D g B (q,y) (χ y • NormalHeatResidual.modelSection t u y))) z =
--         normalGauge J α ht p D g B (q,z)
--           (NormalHeatResidual.residual
--             (fun y => CutoffFamilies.principal (normalPrincipal g B) χ (q,y))
--             (fun y => CutoffFamilies.first (normalPrincipal g B) (gaugedFirst J α ht p D g B) χ (q,y))
--             (fun y => CutoffFamilies.zero (normalPrincipal g B) (gaugedFirst J α ht p D g B)
--               (gaugedZero J α ht p D g B) χ (q,y)) t z u)
--   ```
--
--   **Definitions.** The statement is written with `OAI.TamingCompatibility.MetricModel.Metric` (definitions bundle `OAIQ239Tc000` of this split); `OAI.TamingCompatibility.EuclideanEnergy.V` and `OAI.TamingCompatibility.EuclideanEnergy.e` (definitions bundle `OAIQ239Tc001` of this split); `OAI.TamingCompatibility.HodgeNormalSymbol.Q`, `OAI.TamingCompatibility.HodgeNormalSymbol.W`, `OAI.TamingCompatibility.GeometricHilbert.CutoffFamilies.first`, `OAI.TamingCompatibility.GeometricHilbert.CutoffFamilies.principal`, `OAI.TamingCompatibility.GeometricHilbert.CutoffFamilies.zero`, `OAI.TamingCompatibility.GeometricHilbert.FlatHeat.V`, `OAI.TamingCompatibility.GeometricHilbert.NormalHeatResidual.End`, `OAI.TamingCompatibility.GeometricHilbert.NormalHeatResidual.residual` and `OAI.TamingCompatibility.GeometricHilbert.NormalJets.MetricTensor` (definitions bundle `OAIQ239Tc003` of this split); `OAI.TamingCompatibility.GeometricHilbert.OperatorCalculus.differential` and `OAI.TamingCompatibility.GeometricHilbert.OperatorCalculus.weightedAdjoint` (definitions bundle `OAIQ239Tc004` of this split); `OAI.TamingCompatibility.ManifoldHodge.coordinateMetric` (definitions bundle `OAIQ239Tc006` of this split); `OAI.TamingCompatibility.GeometricHilbert.NormalHeatResidual.modelSection` (definitions bundle `OAIQ239Tc008` of this split); `OAI.TamingCompatibility.GeometricChart.Data` (definitions bundle `OAIQ239Tc011` of this split); `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.gaugedFirst`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.gaugedZero`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalDensity`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalGauge`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalMap`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalPrincipal`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.pulledA` and `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.pulledB` (definitions bundle `OAIQ239Tc014` of this split); `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.ActualData` (definitions bundle `OAIQ239Tc017` of this split); `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.parametrixResidualMetricTensorNormedAddCommGroup` and `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.parametrixResidualMetricTensorNormedSpace` (definitions bundle `OAIQ239Tc019` of this split); `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalDomain` (definitions bundle `OAIQ239Tc021` of this split); `OAI.TamingCompatibility.AlmostComplexStructure`, `OAI.TamingCompatibility.IsSmooth`, `OAI.TamingCompatibility.Model`, `OAI.TamingCompatibility.Space`, `OAI.TamingCompatibility.Tames` and `OAI.TamingCompatibility.TwoForm` (the published bundle `Def_TamingCompatibility`).
--
--   **Used by.** The proof of `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.actual_cutoff_weak_local` of this split imports it.
-- source:
--   OpenAI, Taming implies compatibility on four-manifolds, OpenAI Math Release, October 6, 2026, https://github.com/openai/math (result family 342; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Taming-implies-compatibility-on-four-manifolds-October-6-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/TamingCompatibility/Concentration/HodgeParametrixResidual.lean (declaration OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.actual_cutoff_square_eq)

import Mathlib
import Definitions.Def_TamingCompatibility
import Definitions.Def_OAIQ239Tc019
import Definitions.Def_OAIQ239Tc021

section

attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
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
open scoped Manifold ContDiff Topology RealInnerProductSpace
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
  (p : X) (D : GeometricChart.Data J α ht p)
  (g : Space → MetricTensor (V := Space)) (B : Space → Space →L[ℝ] Space)

attribute [local irreducible] pulledA pulledB normalFirst normalZero normalDensity
  normalPrincipal normalGauge gaugedFirst gaugedZero

attribute [local instance] OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.parametrixResidualMetricTensorNormedAddCommGroup
attribute [local instance] OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.parametrixResidualMetricTensorNormedSpace
lemma actual_cutoff_square_eq (hs : IsSmooth α) (hg : ContDiff ℝ ∞ g) (hB : ContDiff ℝ ∞ B)
    (hsym : ∀ y v w, g y v w = g y w v) {q z : Space}
    (hactual : ActualData J α ht p D q g B)
    (hz : (q,z) ∈ normalDomain J α ht p D g B)
    (hgact : g (normalMap g B q z) = (coordinateMetric J α ht p (normalMap g B q z)).bilinear)
    (χ : Space → ℝ) (hχ : ContDiff ℝ ∞ χ) {t : ℝ} (htpos : 0 < t) (u : W) :
      deriv (fun s => normalGauge J α ht p D g B (q,z) (χ z • NormalHeatResidual.modelSection s u z)) t +
        weightedAdjoint EuclideanEnergy.e (pulledA J α ht p D g B q)
          (pulledB J α ht p D g B q) (fun y => normalDensity g B (q,y))
          (differential EuclideanEnergy.e (pulledA J α ht p D g B q)
            (pulledB J α ht p D g B q)
            (fun y => normalGauge J α ht p D g B (q,y) (χ y • NormalHeatResidual.modelSection t u y))) z =
      normalGauge J α ht p D g B (q,z)
        (NormalHeatResidual.residual
          (fun y => CutoffFamilies.principal (normalPrincipal g B) χ (q,y))
          (fun y => CutoffFamilies.first (normalPrincipal g B) (gaugedFirst J α ht p D g B) χ (q,y))
          (fun y => CutoffFamilies.zero (normalPrincipal g B) (gaugedFirst J α ht p D g B)
            (gaugedZero J α ht p D g B) χ (q,y)) t z u) := by
  sorry

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
end
