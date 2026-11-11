-- Prove2me | Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_GeometricNormalCharts_actual_cutoff_time_integral_local
-- name    : OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.actual_cutoff_time_integral_local
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T22:53:05.063292+00:00
-- url     : https://prove2.me/theorems/2c79ccf7-af11-4ce0-8a33-9a6c871e93fb
-- title:
--   OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.actual_cutoff_time_integral_local: intermediate lemma from OpenAI, Taming implies compatibility on four-manifolds
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.TamingCompatibility.taming_implies_compatibility`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Taming implies compatibility on four-manifolds*, OpenAI Math Release, October 6, 2026, result family 342, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.actual_cutoff_time_integral_local` of [lean/OAI/Geometry/TamingCompatibility/Hodge/HodgeCompactTimeIntegral.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/TamingCompatibility/Hodge/HodgeCompactTimeIntegral.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts`, with `open ManifoldForms NormalJets NormalMetricCalculus CoordinateOperator`, `open HodgeNormalSymbol FirstJetGauge OrthogonalJets Filter Set OperatorCalculus`, `open _root_.MeasureTheory`, `open scoped Manifold ContDiff Topology RealInnerProductSpace`):
--
--   ```lean
--   lemma actual_cutoff_time_integral_local (hg : ContDiff ℝ ∞ g) (hB : ContDiff ℝ ∞ B)
--       (q : Space) (χ : Space → ℝ) (hχ : Continuous χ) (hχc : HasCompactSupport χ)
--       {U : Set Space} (hU : IsOpen U) (hχU : tsupport χ ⊆ U)
--       {t : ℝ} (htpos : 0 < t) (u : W)
--       (η : Space → W) (hη : ContDiffOn ℝ ∞ η U) :
--       HasDerivAt (fun s => ∫ z, normalDensity g B (q,z) * ⟪η z,
--         normalGauge J α ht p D g B (q,z) (χ z • NormalHeatResidual.modelSection s u z)⟫)
--         (∫ z, normalDensity g B (q,z) * ⟪η z,
--           deriv (fun s => normalGauge J α ht p D g B (q,z)
--             (χ z • NormalHeatResidual.modelSection s u z)) t⟫) t
--   ```
--
--   **Definitions.** The statement is written with `OAI.TamingCompatibility.HodgeNormalSymbol.W` and `OAI.TamingCompatibility.GeometricHilbert.NormalJets.MetricTensor` (definitions bundle `OAIQ239Tc003` of this split); `OAI.TamingCompatibility.GeometricHilbert.NormalHeatResidual.modelSection` (definitions bundle `OAIQ239Tc008` of this split); `OAI.TamingCompatibility.GeometricChart.Data` (definitions bundle `OAIQ239Tc011` of this split); `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalDensity` and `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalGauge` (definitions bundle `OAIQ239Tc014` of this split); `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.compactTimeIntegralPatchMetricTensorNormedAddCommGroup` and `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.compactTimeIntegralPatchMetricTensorNormedSpace` (definitions bundle `OAIQ239Tc018` of this split); `OAI.TamingCompatibility.AlmostComplexStructure`, `OAI.TamingCompatibility.Model`, `OAI.TamingCompatibility.Space`, `OAI.TamingCompatibility.Tames` and `OAI.TamingCompatibility.TwoForm` (the published bundle `Def_TamingCompatibility`).
--
--   **Used by.** The proof of `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.ParametrixData.cutoff_form_weak_deriv` of this split imports it.
-- source:
--   OpenAI, Taming implies compatibility on four-manifolds, OpenAI Math Release, October 6, 2026, https://github.com/openai/math (result family 342; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Taming-implies-compatibility-on-four-manifolds-October-6-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/TamingCompatibility/Hodge/HodgeCompactTimeIntegral.lean (declaration OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.actual_cutoff_time_integral_local)

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
open ManifoldForms NormalJets NormalMetricCalculus CoordinateOperator
open HodgeNormalSymbol FirstJetGauge OrthogonalJets Filter Set OperatorCalculus
open _root_.MeasureTheory
open scoped Manifold ContDiff Topology RealInnerProductSpace
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
  (p : X) (D : GeometricChart.Data J α ht p)
  (g : Space → MetricTensor (V := Space)) (B : Space → Space →L[ℝ] Space)
attribute [local irreducible] normalGauge normalFirst

attribute [local instance] OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.compactTimeIntegralPatchMetricTensorNormedAddCommGroup
attribute [local instance] OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.compactTimeIntegralPatchMetricTensorNormedSpace
lemma actual_cutoff_time_integral_local (hg : ContDiff ℝ ∞ g) (hB : ContDiff ℝ ∞ B)
    (q : Space) (χ : Space → ℝ) (hχ : Continuous χ) (hχc : HasCompactSupport χ)
    {U : Set Space} (hU : IsOpen U) (hχU : tsupport χ ⊆ U)
    {t : ℝ} (htpos : 0 < t) (u : W)
    (η : Space → W) (hη : ContDiffOn ℝ ∞ η U) :
    HasDerivAt (fun s => ∫ z, normalDensity g B (q,z) * ⟪η z,
      normalGauge J α ht p D g B (q,z) (χ z • NormalHeatResidual.modelSection s u z)⟫)
      (∫ z, normalDensity g B (q,z) * ⟪η z,
        deriv (fun s => normalGauge J α ht p D g B (q,z)
          (χ z • NormalHeatResidual.modelSection s u z)) t⟫) t := by
  sorry

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
end
