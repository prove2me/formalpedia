-- Prove2me | Theorems.Thm_OAI_ClosedSurfaceR4_JetPolynomial_Perturbation_PolynomialSolveData_metricMeanField_bound
-- name    : OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.metricMeanField_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T12:45:44.628736+00:00
-- url     : https://prove2.me/theorems/cbf778bb-f677-4513-9780-4037a27a009b
-- title:
--   OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.metricMeanField_bound: intermediate lemma from OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.smooth_isometric_immersion`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth isometric immersions of closed surfaces into Euclidean four-space*, OpenAI Math Release, September 23, 2026, result family 333, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.metricMeanField_bound` of [lean/OAI/Geometry/SurfaceImmersion/Correction/ChartedMetricMean.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/SurfaceImmersion/Correction/ChartedMetricMean.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData`, with `open TopologicalSpace`, `open scoped ContDiff NNReal`, `open PhaseMean RealModes WeightedEstimates`):
--
--   ```lean
--   theorem metricMeanField_bound {δ : ℝ} (hδ : 0 < δ)
--       (hτ : 0 < τ) (hs : 0 < (s : ℝ)) (hτs : τ ≤ s) (hs1 : s ≤ 1) (hε : 0 ≤ ε)
--       (hsmall : τ / s + ε / τ ^ tensorLoss P ≤ 1) (q m : ℕ) {A N : ℝ}
--       (hA : 0 ≤ A) (hN : 0 ≤ N)
--       (hn : WeightedBound c.e.target s (m + 1 + (q + 1) * (tensorOrder P + 1)) N (freeNormal c.realMap))
--       (b : SupportedField (F := ℝ) c.chartCompact)
--       (hb : supportedWeightedSeminorm c.chartCompact s (m + 1 + (q + 1) * (tensorOrder P + 1)) b ≤ A) :
--       WeightedBound Set.univ s m
--         (tensorChartBudget m (c.J m) (c.J (m + 1)) *
--           ((τ / s + ε / τ ^ tensorLoss P) * (normalizedMeanBudget (tensorOrder P) c.C c.D q m N * A ^ 2)))
--         (c.metricMeanField δ q b)
--   ```
--
--   **Definitions.** The statement is written with `OAI.ClosedSurfaceR4.JetPolynomial.Base`, `OAI.ClosedSurfaceR4.JetPolynomial.Expression`, `OAI.ClosedSurfaceR4.JetPolynomial.Space`, `OAI.ClosedSurfaceR4.JetPolynomial.SupportedField`, `OAI.ClosedSurfaceR4.JetPolynomial.supportedWeightedSeminorm`, `OAI.ClosedSurfaceR4.PhaseMean.Tensor`, `OAI.ClosedSurfaceR4.WeightedEstimates.WeightedBound`, `OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.tensorLoss` and `OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.tensorOrder` (definitions bundle `OAIQ249SI001` of this split); `OAI.ClosedSurfaceR4.JetPolynomial.tensorChartBudget` and `OAI.ClosedSurfaceR4.RealModes.normalizedMeanBudget` (definitions bundle `OAIQ249SI002` of this split); `OAI.ClosedSurfaceR4.RealModes.RVec`, `OAI.ClosedSurfaceR4.SmallModes.Base`, `OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData` and `OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport` (definitions bundle `OAIQ249SI003` of this split); `OAI.ClosedSurfaceR4.RealModes.freeNormal`, `OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.chartCompact` and `OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.realMap` (definitions bundle `OAIQ249SI007` of this split); `OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.metricMeanField` (definitions bundle `OAIQ249SI012` of this split).
--
--   **Used by.** The proof of `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.uniform_atlas_mean_majorants_fixed_ball` of this split imports it.
-- source:
--   OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 333; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/SurfaceImmersion/Correction/ChartedMetricMean.lean (declaration OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.metricMeanField_bound)

import Mathlib
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Definitions.Def_OAIQ249SI012

section

attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal

namespace ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData
open PhaseMean RealModes WeightedEstimates
variable {n : ℕ} {P : Fin 3 → Fin n → Expression} {ε τ : ℝ}
    {G : Base → Space} {hG : ContDiff ℝ ∞ G} {φ : Base → ℝ}
    {K : Compacts Base} {s : ℝ≥0}
    (c : PolynomialSolveData P ε G hG φ K τ s)

theorem metricMeanField_bound {δ : ℝ} (hδ : 0 < δ)
    (hτ : 0 < τ) (hs : 0 < (s : ℝ)) (hτs : τ ≤ s) (hs1 : s ≤ 1) (hε : 0 ≤ ε)
    (hsmall : τ / s + ε / τ ^ tensorLoss P ≤ 1) (q m : ℕ) {A N : ℝ}
    (hA : 0 ≤ A) (hN : 0 ≤ N)
    (hn : WeightedBound c.e.target s (m + 1 + (q + 1) * (tensorOrder P + 1)) N (freeNormal c.realMap))
    (b : SupportedField (F := ℝ) c.chartCompact)
    (hb : supportedWeightedSeminorm c.chartCompact s (m + 1 + (q + 1) * (tensorOrder P + 1)) b ≤ A) :
    WeightedBound Set.univ s m
      (tensorChartBudget m (c.J m) (c.J (m + 1)) *
        ((τ / s + ε / τ ^ tensorLoss P) * (normalizedMeanBudget (tensorOrder P) c.C c.D q m N * A ^ 2)))
      (c.metricMeanField δ q b) := by
  sorry

end ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData

end

end OAI
end
