-- Prove2me | Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_GeometricNormalCharts_normalDensity_smooth
-- name    : OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalDensity_smooth
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T22:54:39.26237+00:00
-- url     : https://prove2.me/theorems/f2ff987f-73c4-465a-8c83-306c78baaa95
-- title:
--   OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalDensity_smooth: intermediate lemma from OpenAI, Taming implies compatibility on four-manifolds
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.TamingCompatibility.taming_implies_compatibility`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Taming implies compatibility on four-manifolds*, OpenAI Math Release, October 6, 2026, result family 342, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalDensity_smooth` of [lean/OAI/Geometry/TamingCompatibility/Hodge/HodgeCompactExtension.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/TamingCompatibility/Hodge/HodgeCompactExtension.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts`, with `open ManifoldForms ManifoldHodge NormalJets NormalMetricCalculus CoordinateOperator`, `open HodgeNormalSymbol FirstJetGauge OrthogonalJets Filter Set OperatorCalculus UniformJets`, `open scoped Manifold ContDiff Topology RealInnerProductSpace`):
--
--   ```lean
--   lemma normalDensity_smooth (hg : ContDiff ℝ ∞ g) (hB : ContDiff ℝ ∞ B)
--       {x : Space × Space} (hx : normalMetric g B x ∈ regularMetrics) :
--       ContDiffAt ℝ ∞ (normalDensity g B) x
--   ```
--
--   **Definitions.** The statement is written with `OAI.TamingCompatibility.GeometricHilbert.NormalJets.MetricTensor` and `OAI.TamingCompatibility.GeometricHilbert.NormalMetricCalculus.V` (definitions bundle `OAIQ239Tc003` of this split); `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalDensity` and `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalMetric` (definitions bundle `OAIQ239Tc014` of this split); `OAI.TamingCompatibility.GeometricHilbert.NormalMetricCalculus.regularMetrics` (definitions bundle `OAIQ239Tc017` of this split); `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.instNormedAddCommGroupMetricTensorSpace_4` and `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.instNormedSpaceRealMetricTensorSpace_4` (definitions bundle `OAIQ239Tc018` of this split); `OAI.TamingCompatibility.Space` (the published bundle `Def_TamingCompatibility`).
--
--   **Used by.** The proofs of `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.actual_cutoff_square_eq`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.actual_cutoff_weak_local`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.euclidean_angular_near_point`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.gammaNormalWedge_actual_angular`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.gammaNormalWedge_angular`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.globalCandidate_L2_of_bounds`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.globalCorrection_continuous_bounds`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.globalLeading_continuousAt`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.globalLeading_heatBound`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.globalResidual_heatBound`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.kernel_leading_pairing_initial`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.leadingSlice_smooth`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.residualCoordinate_gaussian`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.residualPatch_joint_smooth`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.residualSlice_smooth`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.same_resolvent_smooth_spatial`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.separating_current_angular_moment` and `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.separating_current_euclidean_angular_profile` of this split import it.
-- source:
--   OpenAI, Taming implies compatibility on four-manifolds, OpenAI Math Release, October 6, 2026, https://github.com/openai/math (result family 342; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Taming-implies-compatibility-on-four-manifolds-October-6-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/TamingCompatibility/Hodge/HodgeCompactExtension.lean (declaration OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalDensity_smooth)

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

attribute [local instance] OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.instNormedAddCommGroupMetricTensorSpace_4
attribute [local instance] OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.instNormedSpaceRealMetricTensorSpace_4
lemma normalDensity_smooth (hg : ContDiff ℝ ∞ g) (hB : ContDiff ℝ ∞ B)
    {x : Space × Space} (hx : normalMetric g B x ∈ regularMetrics) :
    ContDiffAt ℝ ∞ (normalDensity g B) x := by
  sorry

attribute [local irreducible] normalFirst

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
end
