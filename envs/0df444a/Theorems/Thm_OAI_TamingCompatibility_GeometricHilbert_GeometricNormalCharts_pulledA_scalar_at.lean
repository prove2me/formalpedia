-- Prove2me | Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_GeometricNormalCharts_pulledA_scalar_at
-- name    : OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.pulledA_scalar_at
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T22:56:46.098747+00:00
-- url     : https://prove2.me/theorems/847ca315-59a7-4456-8a9a-3dc660258355
-- title:
--   OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.pulledA_scalar_at: intermediate lemma from OpenAI, Taming implies compatibility on four-manifolds
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.TamingCompatibility.taming_implies_compatibility`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Taming implies compatibility on four-manifolds*, OpenAI Math Release, October 6, 2026, result family 342, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.pulledA_scalar_at` of [lean/OAI/Geometry/TamingCompatibility/Concentration/HodgeCompactResidual.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/TamingCompatibility/Concentration/HodgeCompactResidual.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts`, with `open ManifoldForms ManifoldHodge NormalJets NormalMetricCalculus CoordinateOperator`, `open HodgeNormalSymbol FirstJetGauge OrthogonalJets Filter Set OperatorCalculus UniformJets`, `open scoped Manifold ContDiff Topology RealInnerProductSpace`):
--
--   ```lean
--   lemma pulledA_scalar_at (hg : ContDiff ℝ ∞ g) (hB : ContDiff ℝ ∞ B)
--       (hsym : ∀ y v w, g y v w = g y w v) {q z : Space}
--       (hx : (q,z) ∈ regularSet J α ht p D g B)
--       (hgact : g (normalMap g B q z) = (coordinateMetric J α ht p (normalMap g B q z)).bilinear)
--       (i j : Fin 4) :
--       (pulledA J α ht p D g B q i z).adjoint ∘L pulledA J α ht p D g B q j z +
--         (pulledA J α ht p D g B q j z).adjoint ∘L pulledA J α ht p D g B q i z =
--         (2*normalPrincipal g B i j (q,z)) • ContinuousLinearMap.id ℝ W
--   ```
--
--   **Definitions.** The statement is written with `OAI.TamingCompatibility.MetricModel.Metric` (definitions bundle `OAIQ239Tc000` of this split); `OAI.TamingCompatibility.HodgeNormalSymbol.Q`, `OAI.TamingCompatibility.HodgeNormalSymbol.W` and `OAI.TamingCompatibility.GeometricHilbert.NormalJets.MetricTensor` (definitions bundle `OAIQ239Tc003` of this split); `OAI.TamingCompatibility.ManifoldHodge.coordinateMetric` (definitions bundle `OAIQ239Tc006` of this split); `OAI.TamingCompatibility.GeometricChart.Data` (definitions bundle `OAIQ239Tc011` of this split); `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalMap`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalPrincipal` and `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.pulledA` (definitions bundle `OAIQ239Tc014` of this split); `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.instNormedAddCommGroupMetricTensorSpace_6`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.instNormedSpaceRealMetricTensorSpace_6` and `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.regularSet` (definitions bundle `OAIQ239Tc018` of this split); `OAI.TamingCompatibility.AlmostComplexStructure`, `OAI.TamingCompatibility.Model`, `OAI.TamingCompatibility.Space`, `OAI.TamingCompatibility.Tames` and `OAI.TamingCompatibility.TwoForm` (the published bundle `Def_TamingCompatibility`).
--
--   **Used by.** The proof of `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.actual_cutoff_square_eq` of this split imports it.
-- source:
--   OpenAI, Taming implies compatibility on four-manifolds, OpenAI Math Release, October 6, 2026, https://github.com/openai/math (result family 342; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Taming-implies-compatibility-on-four-manifolds-October-6-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/TamingCompatibility/Concentration/HodgeCompactResidual.lean (declaration OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.pulledA_scalar_at)

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

attribute [local instance] OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.instNormedAddCommGroupMetricTensorSpace_6
attribute [local instance] OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.instNormedSpaceRealMetricTensorSpace_6
lemma pulledA_scalar_at (hg : ContDiff ℝ ∞ g) (hB : ContDiff ℝ ∞ B)
    (hsym : ∀ y v w, g y v w = g y w v) {q z : Space}
    (hx : (q,z) ∈ regularSet J α ht p D g B)
    (hgact : g (normalMap g B q z) = (coordinateMetric J α ht p (normalMap g B q z)).bilinear)
    (i j : Fin 4) :
    (pulledA J α ht p D g B q i z).adjoint ∘L pulledA J α ht p D g B q j z +
      (pulledA J α ht p D g B q j z).adjoint ∘L pulledA J α ht p D g B q i z =
      (2*normalPrincipal g B i j (q,z)) • ContinuousLinearMap.id ℝ W := by
  sorry

attribute [local irreducible] pulledA pulledB normalFirst normalZero normalDensity
  normalPrincipal normalGauge gaugedFirst gaugedZero

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
end
