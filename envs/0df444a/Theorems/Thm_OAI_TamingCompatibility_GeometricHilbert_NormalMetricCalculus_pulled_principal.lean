-- Prove2me | Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_NormalMetricCalculus_pulled_principal
-- name    : OAI.TamingCompatibility.GeometricHilbert.NormalMetricCalculus.pulled_principal
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T22:17:04.249398+00:00
-- url     : https://prove2.me/theorems/d2e3e1ed-1955-47ce-9625-c8dcf310197d
-- title:
--   OAI.TamingCompatibility.GeometricHilbert.NormalMetricCalculus.pulled_principal: intermediate lemma from OpenAI, Taming implies compatibility on four-manifolds
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.TamingCompatibility.taming_implies_compatibility`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Taming implies compatibility on four-manifolds*, OpenAI Math Release, October 6, 2026, result family 342, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.TamingCompatibility.GeometricHilbert.NormalMetricCalculus.pulled_principal` of [lean/OAI/Geometry/TamingCompatibility/Charts/FirstJetGauge.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/TamingCompatibility/Charts/FirstJetGauge.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.TamingCompatibility.GeometricHilbert.NormalMetricCalculus`, with `open scoped RealInnerProductSpace`, `open NormalJets CoordinateOperator HodgeNormalSymbol`):
--
--   ```lean
--   lemma pulled_principal (g : MetricModel.Metric V) (b : Fin 4 → V)
--       (hb : ∀ i j, g.bilinear (b i) (b j) = if i=j then 1 else 0)
--       (L : V ≃L[ℝ] V) (i j : Fin 4) :
--       (pullCoefficient (HodgeFrozenEnergy.coefficient b) L.symm.toContinuousLinearMap i).adjoint ∘L
--         pullCoefficient (HodgeFrozenEnergy.coefficient b) L.symm.toContinuousLinearMap j +
--       (pullCoefficient (HodgeFrozenEnergy.coefficient b) L.symm.toContinuousLinearMap j).adjoint ∘L
--         pullCoefficient (HodgeFrozenEnergy.coefficient b) L.symm.toContinuousLinearMap i =
--         (2 * principal (MetricDensity.pullMetric g.bilinear L.toContinuousLinearMap) i j) •
--           ContinuousLinearMap.id ℝ W
--   ```
--
--   **Definitions.** The statement is written with `OAI.TamingCompatibility.MetricModel.Metric` (definitions bundle `OAIQ239Tc000` of this split); `OAI.TamingCompatibility.HodgeNormalSymbol.Q`, `OAI.TamingCompatibility.HodgeNormalSymbol.W`, `OAI.TamingCompatibility.MetricDensity.pullMetric`, `OAI.TamingCompatibility.GeometricHilbert.NormalMetricCalculus.V` and `OAI.TamingCompatibility.GeometricHilbert.NormalMetricCalculus.principal` (definitions bundle `OAIQ239Tc003` of this split); `OAI.TamingCompatibility.HodgeFrozenEnergy.coefficient` and `OAI.TamingCompatibility.GeometricHilbert.CoordinateOperator.pullCoefficient` (definitions bundle `OAIQ239Tc007` of this split).
--
--   **Used by.** The proof of `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.pulledA_weighted_principal` of this split imports it.
-- source:
--   OpenAI, Taming implies compatibility on four-manifolds, OpenAI Math Release, October 6, 2026, https://github.com/openai/math (result family 342; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Taming-implies-compatibility-on-four-manifolds-October-6-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/TamingCompatibility/Charts/FirstJetGauge.lean (declaration OAI.TamingCompatibility.GeometricHilbert.NormalMetricCalculus.pulled_principal)

import Mathlib
import Definitions.Def_OAIQ239Tc007

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace TamingCompatibility.GeometricHilbert.NormalMetricCalculus
open scoped RealInnerProductSpace
open NormalJets CoordinateOperator HodgeNormalSymbol
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace

lemma pulled_principal (g : MetricModel.Metric V) (b : Fin 4 → V)
    (hb : ∀ i j, g.bilinear (b i) (b j) = if i=j then 1 else 0)
    (L : V ≃L[ℝ] V) (i j : Fin 4) :
    (pullCoefficient (HodgeFrozenEnergy.coefficient b) L.symm.toContinuousLinearMap i).adjoint ∘L
      pullCoefficient (HodgeFrozenEnergy.coefficient b) L.symm.toContinuousLinearMap j +
    (pullCoefficient (HodgeFrozenEnergy.coefficient b) L.symm.toContinuousLinearMap j).adjoint ∘L
      pullCoefficient (HodgeFrozenEnergy.coefficient b) L.symm.toContinuousLinearMap i =
      (2 * principal (MetricDensity.pullMetric g.bilinear L.toContinuousLinearMap) i j) •
        ContinuousLinearMap.id ℝ W := by
  sorry

end TamingCompatibility.GeometricHilbert.NormalMetricCalculus

end

end OAI
end
