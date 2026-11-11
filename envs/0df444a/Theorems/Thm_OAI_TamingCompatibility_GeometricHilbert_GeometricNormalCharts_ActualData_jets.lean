-- Prove2me | Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_GeometricNormalCharts_ActualData_jets
-- name    : OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.ActualData.jets
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T22:55:44.24938+00:00
-- url     : https://prove2.me/theorems/a8aa4913-d88f-4e27-a4f1-954535dfb920
-- title:
--   OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.ActualData.jets: intermediate lemma from OpenAI, Taming implies compatibility on four-manifolds
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.TamingCompatibility.taming_implies_compatibility`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Taming implies compatibility on four-manifolds*, OpenAI Math Release, October 6, 2026, result family 342, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.ActualData.jets` of [lean/OAI/Geometry/TamingCompatibility/DifferentialForms/FirstMatrixJoint.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/TamingCompatibility/DifferentialForms/FirstMatrixJoint.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts`, with `open ManifoldForms ManifoldHodge NormalJets NormalMetricCalculus CoordinateOperator`, `open HodgeNormalSymbol FirstJetGauge OrthogonalJets Filter Set OperatorCalculus UniformJets`, `open scoped Manifold ContDiff Topology RealInnerProductSpace`):
--
--   ```lean
--   lemma ActualData.jets (J : AlmostComplexStructure X) (α : TwoForm X)
--       (hs : IsSmooth α) (ht : Tames α J) (p : X) (D : GeometricChart.Data J α ht p)
--       (q : Space) (g : Space → MetricTensor (V := Space)) (B : Space → Space →L[ℝ] Space)
--       (hg : ContDiff ℝ ∞ g) (hB : ContDiff ℝ ∞ B) (hactual : ActualData J α ht p D q g B) :
--         (∀ i, ContDiffAt ℝ ∞ (pulledA J α ht p D g B q i) 0) ∧
--         ContDiffAt ℝ ∞ (pulledB J α ht p D g B q) 0 ∧
--         (let m := fun z => normalMetric g B (q,z)
--          let ρ := fun z => volumeDensity (m z)
--          ContDiffAt ℝ ∞ ρ 0 ∧ ρ 0 = 1 ∧ fderiv ℝ ρ 0 = 0 ∧
--          (∀ i j, ContDiffAt ℝ ∞ (fun z => principal (m z) i j) 0 ∧
--            principal (m 0) i j = (if i=j then 1 else 0) ∧
--            fderiv ℝ (fun z => principal (m z) i j) 0 = 0) ∧
--          (∀ j, (actualSquareFirst EuclideanEnergy.e (pulledA J α ht p D g B q)
--              (pulledB J α ht p D g B q) ρ j 0).adjoint =
--            -actualSquareFirst EuclideanEnergy.e (pulledA J α ht p D g B q)
--              (pulledB J α ht p D g B q) ρ j 0))
--   ```
--
--   **Definitions.** The statement is written with `OAI.TamingCompatibility.EuclideanEnergy.V` and `OAI.TamingCompatibility.EuclideanEnergy.e` (definitions bundle `OAIQ239Tc001` of this split); `OAI.TamingCompatibility.HodgeNormalSymbol.Q`, `OAI.TamingCompatibility.HodgeNormalSymbol.W`, `OAI.TamingCompatibility.GeometricHilbert.FirstJetGauge.End`, `OAI.TamingCompatibility.GeometricHilbert.FirstJetGauge.actualSquareFirst`, `OAI.TamingCompatibility.GeometricHilbert.NormalJets.MetricTensor`, `OAI.TamingCompatibility.GeometricHilbert.NormalMetricCalculus.principal` and `OAI.TamingCompatibility.GeometricHilbert.NormalMetricCalculus.volumeDensity` (definitions bundle `OAIQ239Tc003` of this split); `OAI.TamingCompatibility.GeometricChart.Data` (definitions bundle `OAIQ239Tc011` of this split); `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalMetric`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.pulledA` and `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.pulledB` (definitions bundle `OAIQ239Tc014` of this split); `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.ActualData` (definitions bundle `OAIQ239Tc017` of this split); `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.firstMatrixJointMetricTensorNormedAddCommGroup` and `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.firstMatrixJointMetricTensorNormedSpace` (definitions bundle `OAIQ239Tc018` of this split); `OAI.TamingCompatibility.AlmostComplexStructure`, `OAI.TamingCompatibility.IsSmooth`, `OAI.TamingCompatibility.Model`, `OAI.TamingCompatibility.Space`, `OAI.TamingCompatibility.Tames` and `OAI.TamingCompatibility.TwoForm` (the published bundle `Def_TamingCompatibility`).
--
--   **Used by.** The proofs of `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.gaugedFirst_center` and `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalGauge_unitary` of this split import it.
-- source:
--   OpenAI, Taming implies compatibility on four-manifolds, OpenAI Math Release, October 6, 2026, https://github.com/openai/math (result family 342; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Taming-implies-compatibility-on-four-manifolds-October-6-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/TamingCompatibility/DifferentialForms/FirstMatrixJoint.lean (declaration OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.ActualData.jets)

import Mathlib
import Definitions.Def_TamingCompatibility
import Definitions.Def_OAIQ239Tc017
import Definitions.Def_OAIQ239Tc018

section

attribute [-instance] _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge NormalJets NormalMetricCalculus CoordinateOperator
open HodgeNormalSymbol FirstJetGauge OrthogonalJets Filter Set OperatorCalculus UniformJets
open scoped Manifold ContDiff Topology RealInnerProductSpace
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]

attribute [local instance] OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.firstMatrixJointMetricTensorNormedAddCommGroup
attribute [local instance] OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.firstMatrixJointMetricTensorNormedSpace
lemma ActualData.jets (J : AlmostComplexStructure X) (α : TwoForm X)
    (hs : IsSmooth α) (ht : Tames α J) (p : X) (D : GeometricChart.Data J α ht p)
    (q : Space) (g : Space → MetricTensor (V := Space)) (B : Space → Space →L[ℝ] Space)
    (hg : ContDiff ℝ ∞ g) (hB : ContDiff ℝ ∞ B) (hactual : ActualData J α ht p D q g B) :
      (∀ i, ContDiffAt ℝ ∞ (pulledA J α ht p D g B q i) 0) ∧
      ContDiffAt ℝ ∞ (pulledB J α ht p D g B q) 0 ∧
      (let m := fun z => normalMetric g B (q,z)
       let ρ := fun z => volumeDensity (m z)
       ContDiffAt ℝ ∞ ρ 0 ∧ ρ 0 = 1 ∧ fderiv ℝ ρ 0 = 0 ∧
       (∀ i j, ContDiffAt ℝ ∞ (fun z => principal (m z) i j) 0 ∧
         principal (m 0) i j = (if i=j then 1 else 0) ∧
         fderiv ℝ (fun z => principal (m z) i j) 0 = 0) ∧
       (∀ j, (actualSquareFirst EuclideanEnergy.e (pulledA J α ht p D g B q)
           (pulledB J α ht p D g B q) ρ j 0).adjoint =
         -actualSquareFirst EuclideanEnergy.e (pulledA J α ht p D g B q)
           (pulledB J α ht p D g B q) ρ j 0)) := by
  sorry

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end

end OAI
end
