-- Prove2me | Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_GeometricNormalCharts_pulledA_weighted_principal
-- name    : OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.pulledA_weighted_principal
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T22:57:56.751306+00:00
-- url     : https://prove2.me/theorems/cfae1df1-245f-4ffb-89c1-cb8fc1938507
-- title:
--   OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.pulledA_weighted_principal: intermediate lemma from OpenAI, Taming implies compatibility on four-manifolds
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.TamingCompatibility.taming_implies_compatibility`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Taming implies compatibility on four-manifolds*, OpenAI Math Release, October 6, 2026, result family 342, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.pulledA_weighted_principal` of [lean/OAI/Geometry/TamingCompatibility/Functional/NormalMap.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/TamingCompatibility/Functional/NormalMap.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts`, with `open ManifoldForms ManifoldHodge NormalJets NormalMetricCalculus CoordinateOperator`, `open HodgeNormalSymbol FirstJetGauge Filter`, `open scoped Manifold ContDiff Topology RealInnerProductSpace`):
--
--   ```lean
--   lemma pulledA_weighted_principal (J : AlmostComplexStructure X) (α : TwoForm X)
--       (ht : Tames α J) (p : X) (D : GeometricChart.Data J α ht p)
--       (g : Space → MetricTensor (V := Space)) (B : Space → Space →L[ℝ] Space)
--       (hg : ContDiff ℝ ∞ g) (hB : ContDiff ℝ ∞ B)
--       (hsym : ∀ x v w, g x v w = g x w v)
--       (U : Set Space) (hU : IsOpen U) (hUD : U ⊆ D.domain)
--       (hgact : ∀ x ∈ U, g x = (coordinateMetric J α ht p x).bilinear)
--       (q : Space) (hq : q ∈ U) (hBq : (B q).IsInvertible) (i j : Fin 4) :
--       let ρ := fun z => volumeDensity (normalMetric g B (q,z))
--       let a := pulledA J α ht p D g B q
--       (fun z => weightedPrincipal a ρ i j z + weightedPrincipal a ρ j i z) =ᶠ[𝓝 0]
--         (fun z => (2*(ρ z*principal (normalMetric g B (q,z)) i j)) •
--           ContinuousLinearMap.id ℝ W)
--   ```
--
--   **Definitions.** The statement is written with `OAI.TamingCompatibility.MetricModel.Metric` (definitions bundle `OAIQ239Tc000` of this split); `OAI.TamingCompatibility.HodgeNormalSymbol.Q`, `OAI.TamingCompatibility.HodgeNormalSymbol.W`, `OAI.TamingCompatibility.GeometricHilbert.FirstJetGauge.End`, `OAI.TamingCompatibility.GeometricHilbert.FirstJetGauge.weightedPrincipal`, `OAI.TamingCompatibility.GeometricHilbert.NormalJets.MetricTensor`, `OAI.TamingCompatibility.GeometricHilbert.NormalMetricCalculus.principal` and `OAI.TamingCompatibility.GeometricHilbert.NormalMetricCalculus.volumeDensity` (definitions bundle `OAIQ239Tc003` of this split); `OAI.TamingCompatibility.ManifoldHodge.coordinateMetric` (definitions bundle `OAIQ239Tc006` of this split); `OAI.TamingCompatibility.GeometricChart.Data` (definitions bundle `OAIQ239Tc011` of this split); `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalMetric` and `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.pulledA` (definitions bundle `OAIQ239Tc014` of this split); `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.instNormedAddCommGroupMetricTensorSpace_2` and `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.instNormedSpaceRealMetricTensorSpace_2` (definitions bundle `OAIQ239Tc018` of this split); `OAI.TamingCompatibility.AlmostComplexStructure`, `OAI.TamingCompatibility.Model`, `OAI.TamingCompatibility.Space`, `OAI.TamingCompatibility.Tames` and `OAI.TamingCompatibility.TwoForm` (the published bundle `Def_TamingCompatibility`).
--
--   **Used by.** The proof of `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.ActualData.jets` of this split imports it.
-- source:
--   OpenAI, Taming implies compatibility on four-manifolds, OpenAI Math Release, October 6, 2026, https://github.com/openai/math (result family 342; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Taming-implies-compatibility-on-four-manifolds-October-6-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/TamingCompatibility/Functional/NormalMap.lean (declaration OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.pulledA_weighted_principal)

import Mathlib
import Definitions.Def_TamingCompatibility
import Definitions.Def_OAIQ239Tc018

section

attribute [-instance] _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
noncomputable section
section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge NormalJets NormalMetricCalculus CoordinateOperator
open HodgeNormalSymbol FirstJetGauge Filter
open scoped Manifold ContDiff Topology RealInnerProductSpace
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace

variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]

attribute [local instance] OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.instNormedAddCommGroupMetricTensorSpace_2
attribute [local instance] OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.instNormedSpaceRealMetricTensorSpace_2
lemma pulledA_weighted_principal (J : AlmostComplexStructure X) (α : TwoForm X)
    (ht : Tames α J) (p : X) (D : GeometricChart.Data J α ht p)
    (g : Space → MetricTensor (V := Space)) (B : Space → Space →L[ℝ] Space)
    (hg : ContDiff ℝ ∞ g) (hB : ContDiff ℝ ∞ B)
    (hsym : ∀ x v w, g x v w = g x w v)
    (U : Set Space) (hU : IsOpen U) (hUD : U ⊆ D.domain)
    (hgact : ∀ x ∈ U, g x = (coordinateMetric J α ht p x).bilinear)
    (q : Space) (hq : q ∈ U) (hBq : (B q).IsInvertible) (i j : Fin 4) :
    let ρ := fun z => volumeDensity (normalMetric g B (q,z))
    let a := pulledA J α ht p D g B q
    (fun z => weightedPrincipal a ρ i j z + weightedPrincipal a ρ j i z) =ᶠ[𝓝 0]
      (fun z => (2*(ρ z*principal (normalMetric g B (q,z)) i j)) •
        ContinuousLinearMap.id ℝ W) := by
  sorry

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end
end
end
end
end
end
end
end
end
end

end OAI
end
