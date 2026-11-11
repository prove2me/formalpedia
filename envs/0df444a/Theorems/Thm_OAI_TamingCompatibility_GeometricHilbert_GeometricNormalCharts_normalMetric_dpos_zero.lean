-- Prove2me | Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_GeometricNormalCharts_normalMetric_dpos_zero
-- name    : OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalMetric_dpos_zero
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T22:52:42.043613+00:00
-- url     : https://prove2.me/theorems/e9235018-142a-4822-815d-962be5d1f9cd
-- title:
--   OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalMetric_dpos_zero: intermediate lemma from OpenAI, Taming implies compatibility on four-manifolds
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.TamingCompatibility.taming_implies_compatibility`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Taming implies compatibility on four-manifolds*, OpenAI Math Release, October 6, 2026, result family 342, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalMetric_dpos_zero` of [lean/OAI/Geometry/TamingCompatibility/DifferentialForms/Dpos.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/TamingCompatibility/DifferentialForms/Dpos.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts`, with `open ManifoldForms ManifoldHodge _root_.MeasureTheory Set Filter NormalJets`, `open scoped Manifold ContDiff Topology RealInnerProductSpace`):
--
--   ```lean
--   lemma normalMetric_dpos_zero (g : Space → MetricTensor (V := Space))
--       (B : Space → Space →L[ℝ] Space) (hg : ContDiff ℝ ∞ g) (hB : ContDiff ℝ ∞ B)
--       (hsym : ∀ x v w, g x v w = g x w v) (p : Space)
--       (hzero : affineMetric g B (p,0) = innerSL ℝ (E := Space)) :
--       UniformJets.dpos (normalMetric g B) (p,0) = 0
--   ```
--
--   **Definitions.** The statement is written with `OAI.TamingCompatibility.GeometricHilbert.NormalJets.MetricTensor` and `OAI.TamingCompatibility.GeometricHilbert.UniformJets.dpos` (definitions bundle `OAIQ239Tc003` of this split); `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.affineMetric`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.instNormedAddCommGroupMetricTensorSpace`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.instNormedSpaceRealMetricTensorSpace` and `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalMetric` (definitions bundle `OAIQ239Tc014` of this split); `OAI.TamingCompatibility.Space` (the published bundle `Def_TamingCompatibility`).
--
--   **Used by.** The proof of `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normal_density_principal_jets` of this split imports it.
-- source:
--   OpenAI, Taming implies compatibility on four-manifolds, OpenAI Math Release, October 6, 2026, https://github.com/openai/math (result family 342; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Taming-implies-compatibility-on-four-manifolds-October-6-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/TamingCompatibility/DifferentialForms/Dpos.lean (declaration OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalMetric_dpos_zero)

import Mathlib
import Definitions.Def_TamingCompatibility
import Definitions.Def_OAIQ239Tc014

section

attribute [-instance] _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
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
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge _root_.MeasureTheory Set Filter NormalJets
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace

attribute [local instance] OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.instNormedAddCommGroupMetricTensorSpace
attribute [local instance] OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.instNormedSpaceRealMetricTensorSpace
local instance instNormedAddCommGroupMetricDerivativeSpace_rdb305d_1 : NormedAddCommGroup (NormalJets.MetricDerivative (V := ManifoldForms.Space)) := ContinuousLinearMap.toNormedAddCommGroup
local instance instNormedSpaceRealMetricDerivativeSpace_rdb305d_1 : NormedSpace ℝ (NormalJets.MetricDerivative (V := ManifoldForms.Space)) := ContinuousLinearMap.toNormedSpace
lemma normalMetric_dpos_zero (g : Space → MetricTensor (V := Space))
    (B : Space → Space →L[ℝ] Space) (hg : ContDiff ℝ ∞ g) (hB : ContDiff ℝ ∞ B)
    (hsym : ∀ x v w, g x v w = g x w v) (p : Space)
    (hzero : affineMetric g B (p,0) = innerSL ℝ (E := Space)) :
    UniformJets.dpos (normalMetric g B) (p,0) = 0 := by
  sorry

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end
end
end
end
end

end OAI
end
