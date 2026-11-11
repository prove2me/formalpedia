-- Prove2me | Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_GeometricNormalCharts_leadingSliceForm_weak_deriv
-- name    : OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.leadingSliceForm_weak_deriv
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T23:22:03.477267+00:00
-- url     : https://prove2.me/theorems/7139d2fd-388d-49ab-9001-87218da1268b
-- title:
--   OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.leadingSliceForm_weak_deriv: intermediate lemma from OpenAI, Taming implies compatibility on four-manifolds
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.TamingCompatibility.taming_implies_compatibility`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Taming implies compatibility on four-manifolds*, OpenAI Math Release, October 6, 2026, result family 342, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.leadingSliceForm_weak_deriv` of [lean/OAI/Geometry/TamingCompatibility/Hodge/HodgePatchPairing.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/TamingCompatibility/Hodge/HodgePatchPairing.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts`, with `open ManifoldForms ManifoldHodge ManifoldLocalization ManifoldVolume NormalJets NormalMetricCalculus CoordinateOperator`, `open HodgeNormalSymbol FirstJetGauge OrthogonalJets Filter Set OperatorCalculus UniformJets`, `open _root_.MeasureTheory`, `open scoped Manifold ContDiff Topology RealInnerProductSpace`):
--
--   ```lean
--   lemma leadingSliceForm_weak_deriv (hs : IsSmooth α) (p : A.centers) {q : Space}
--       (hq : q ∈ Metric.closedBall (extChartAt Model p.val p.val) (E p).radius)
--       {t : ℝ} (htp : 0 < t) (u : W) (a : TwoForm X) (ha : IsSmooth a) :
--       HasDerivAt (fun s => ∫ x, GeometricAdjoint.pairing J α ht a
--           (leadingSliceForm J α ht A E p q s u) x ∂geometricVolume A J α)
--         ((∫ x, GeometricAdjoint.pairing J α ht a
--           (residualSliceForm J α ht A E p q t u) x ∂geometricVolume A J α) -
--          (∫ x, HodgeChart.energyPairing J α ht a
--           (leadingSliceForm J α ht A E p q t u) x ∂geometricVolume A J α)) t
--   ```
--
--   **Definitions.** The statement is written with `OAI.TamingCompatibility.HodgeNormalSymbol.W`, `OAI.TamingCompatibility.ManifoldLocalization.FiniteCharts` and `OAI.TamingCompatibility.ManifoldVolume.geometricVolume` (definitions bundle `OAIQ239Tc003` of this split); `OAI.TamingCompatibility.GeometricAdjoint.pairing` (definitions bundle `OAIQ239Tc014` of this split); `OAI.TamingCompatibility.HodgeChart.energyPairing` (definitions bundle `OAIQ239Tc019` of this split); `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.ParametrixData`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.leadingSliceForm`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.residualSliceForm` and `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.ParametrixData.source` (definitions bundle `OAIQ239Tc021` of this split); `OAI.TamingCompatibility.AlmostComplexStructure`, `OAI.TamingCompatibility.IsSmooth`, `OAI.TamingCompatibility.Model`, `OAI.TamingCompatibility.Space`, `OAI.TamingCompatibility.Tames` and `OAI.TamingCompatibility.TwoForm` (the published bundle `Def_TamingCompatibility`).
--
--   **Used by.** The proof of `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.leadingKernelForm_weak_laplacian` of this split imports it.
-- source:
--   OpenAI, Taming implies compatibility on four-manifolds, OpenAI Math Release, October 6, 2026, https://github.com/openai/math (result family 342; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Taming-implies-compatibility-on-four-manifolds-October-6-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/TamingCompatibility/Hodge/HodgePatchPairing.lean (declaration OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.leadingSliceForm_weak_deriv)

import Mathlib
import Definitions.Def_TamingCompatibility
import Definitions.Def_OAIQ239Tc019
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
  normalPrincipal gaugedFirst gaugedZero NormalHeatResidual.residual
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [T2Space X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
  (A : FiniteCharts X) (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)

variable [MeasurableSpace X] [BorelSpace X]

local instance instNormedAddCommGroupMetricTensorSpace_14_r741cb2_1 : NormedAddCommGroup (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedAddCommGroup
local instance instNormedSpaceRealMetricTensorSpace_14_r741cb2_1 : NormedSpace ℝ (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedSpace
include hE in
lemma leadingSliceForm_weak_deriv (hs : IsSmooth α) (p : A.centers) {q : Space}
    (hq : q ∈ Metric.closedBall (extChartAt Model p.val p.val) (E p).radius)
    {t : ℝ} (htp : 0 < t) (u : W) (a : TwoForm X) (ha : IsSmooth a) :
    HasDerivAt (fun s => ∫ x, GeometricAdjoint.pairing J α ht a
        (leadingSliceForm J α ht A E p q s u) x ∂geometricVolume A J α)
      ((∫ x, GeometricAdjoint.pairing J α ht a
        (residualSliceForm J α ht A E p q t u) x ∂geometricVolume A J α) -
       (∫ x, HodgeChart.energyPairing J α ht a
        (leadingSliceForm J α ht A E p q t u) x ∂geometricVolume A J α)) t := by
  sorry

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
end
