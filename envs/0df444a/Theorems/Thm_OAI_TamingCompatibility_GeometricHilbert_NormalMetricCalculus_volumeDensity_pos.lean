-- Prove2me | Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_NormalMetricCalculus_volumeDensity_pos
-- name    : OAI.TamingCompatibility.GeometricHilbert.NormalMetricCalculus.volumeDensity_pos
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T23:11:21.794444+00:00
-- url     : https://prove2.me/theorems/9a9451ee-6a6c-4f72-a854-02f81545a722
-- title:
--   OAI.TamingCompatibility.GeometricHilbert.NormalMetricCalculus.volumeDensity_pos: intermediate lemma from OpenAI, Taming implies compatibility on four-manifolds
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.TamingCompatibility.taming_implies_compatibility`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Taming implies compatibility on four-manifolds*, OpenAI Math Release, October 6, 2026, result family 342, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.TamingCompatibility.GeometricHilbert.NormalMetricCalculus.volumeDensity_pos` of [lean/OAI/Geometry/TamingCompatibility/DifferentialForms/FirstMatrixJoint.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/TamingCompatibility/DifferentialForms/FirstMatrixJoint.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.TamingCompatibility.GeometricHilbert.NormalMetricCalculus`, with `open NormalJets MetricDensity Filter Set`, `open scoped ContDiff Topology`):
--
--   ```lean
--   lemma volumeDensity_pos {M : MetricTensor (V := V)} (hM : M ∈ regularMetrics) :
--       0 < volumeDensity M
--   ```
--
--   **Definitions.** The statement is written with `OAI.TamingCompatibility.GeometricHilbert.NormalJets.MetricTensor`, `OAI.TamingCompatibility.GeometricHilbert.NormalMetricCalculus.V` and `OAI.TamingCompatibility.GeometricHilbert.NormalMetricCalculus.volumeDensity` (definitions bundle `OAIQ239Tc003` of this split); `OAI.TamingCompatibility.GeometricHilbert.NormalMetricCalculus.regularMetrics` (definitions bundle `OAIQ239Tc017` of this split).
--
--   **Used by.** The proofs of `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.actual_cutoff_square_eq`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.actual_cutoff_weak_local`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.euclidean_angular_near_point`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.gammaNormalWedge_actual_angular`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.gammaNormalWedge_angular`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.globalCandidate_L2_of_bounds`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.globalCorrection_continuous_bounds`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.globalLeading_continuousAt`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.globalLeading_heatBound`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.globalResidual_heatBound`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.kernel_leading_pairing_initial`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.leadingSlice_smooth`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.residualCoordinate_gaussian`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.residualPatch_joint_smooth`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.residualSlice_smooth`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.same_resolvent_smooth_spatial`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.separating_current_angular_moment` and `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.separating_current_euclidean_angular_profile` of this split import it.
-- source:
--   OpenAI, Taming implies compatibility on four-manifolds, OpenAI Math Release, October 6, 2026, https://github.com/openai/math (result family 342; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Taming-implies-compatibility-on-four-manifolds-October-6-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/TamingCompatibility/DifferentialForms/FirstMatrixJoint.lean (declaration OAI.TamingCompatibility.GeometricHilbert.NormalMetricCalculus.volumeDensity_pos)

import Mathlib
import Definitions.Def_OAIQ239Tc017

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace TamingCompatibility.GeometricHilbert.NormalMetricCalculus
open NormalJets MetricDensity Filter Set
open scoped ContDiff Topology
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace

local instance instNormedAddCommGroupMetricTensorV_1_rc32f74_1 : NormedAddCommGroup (MetricTensor (V := V)) := ContinuousLinearMap.toNormedAddCommGroup
local instance instNormedSpaceRealMetricTensorV_1_rc32f74_1 : NormedSpace ℝ (MetricTensor (V := V)) := ContinuousLinearMap.toNormedSpace
lemma volumeDensity_pos {M : MetricTensor (V := V)} (hM : M ∈ regularMetrics) :
    0 < volumeDensity M := by
  sorry

end TamingCompatibility.GeometricHilbert.NormalMetricCalculus

end

end OAI
end
