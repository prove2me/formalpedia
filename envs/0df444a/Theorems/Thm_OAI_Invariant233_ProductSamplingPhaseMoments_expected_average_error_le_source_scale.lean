-- Prove2me | Theorems.Thm_OAI_Invariant233_ProductSamplingPhaseMoments_expected_average_error_le_source_scale
-- name    : OAI.Invariant233.ProductSamplingPhaseMoments.expected_average_error_le_source_scale
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T19:31:47.213642+00:00
-- url     : https://prove2.me/theorems/9bc0fb6e-63e8-4355-a37a-f570d0a24108
-- title:
--   OAI.Invariant233.ProductSamplingPhaseMoments.expected_average_error_le_source_scale: intermediate lemma from OpenAI, Invariant-projection counterexamples for every irrational rotation
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Invariant233.Results.prescribed_irrational_counterexample` and `OAI.Invariant233.Results.product_realization`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Invariant-projection counterexamples for every irrational rotation*, OpenAI Math Release, September 27, 2026, result family 293, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Invariant233.ProductSamplingPhaseMoments.expected_average_error_le_source_scale` of [lean/OAI/Analysis/IrrationalRotation/Sampling/ProductSamplingNumericalBudget.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/IrrationalRotation/Sampling/ProductSamplingNumericalBudget.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Invariant233.ProductSamplingPhaseMoments`, with `open MeasureTheory Set`):
--
--   ```lean
--   theorem expected_average_error_le_source_scale {κ : Type*} [Fintype κ]
--       {p : ProductScaleData} (hp : ProductScaleLaws p) {j : ℕ} (hm : 200 ≤ p.m j)
--       (N₀ : κ → ℝ) (hN : ∀ i, 0 < N₀ i) (hNle : ∀ i, N₀ i ≤ p.N j)
--       (powers : Finset ℕ) (hs : ProductSamplingPowersAt p j powers)
--       (u : κ → ℝ → ℝ → ℝ) (C : κ → ℝ)
--       (hu : ∀ i, Measurable (Function.uncurry (u i)))
--       (hbound : ∀ i s t, |u i s t| ≤ C i)
--       (hzero : ∀ i s t, 0 ≤ u i s t)
--       (hmean : ∀ i s, mean (u i) s ≤ 2)
--       (hBV : ∀ i s, s ∈ Ico (0 : ℝ) 1 → BoundedVariationOn (u i s) (Icc (0 : ℝ) 1))
--       (hV : ∀ i s, s ∈ Ico (0 : ℝ) 1 → realBVSize (u i s) ≤ 16 * (p.m j : ℝ)^10)
--       (hbase : ∀ i, (∫ s, (mean (u i) s)^2 ∂unitInterval) ≤
--         1 + ((p.m j : ℝ)^(-(3 / 5 : ℝ)))^2 / (1 - (p.m j : ℝ)^(-(3 / 5 : ℝ)))^2)
--       {D : ℝ}
--       (hsquare : ∀ i, (∫ s, ∫ t, (u i s t)^2 ∂unitInterval ∂unitInterval) ≤ D) :
--       (∫ a, ∫ x, ((powers.card : ℝ)⁻¹ *
--           (∑ n ∈ powers, ∏ i, u i (x i) (Int.fract ((n : ℝ) * a i))) -
--           ∏ i, mean (u i) (x i))^2
--         ∂Measure.pi (fun _ : κ => unitInterval)
--         ∂Measure.pi (fun i => UniformIntervalPhase.lambdaLaw (N₀ i))) ≤
--         (2 * D)^Fintype.card κ / (powers.card : ℝ) +
--           3 * ((Fintype.card κ : ℝ) * (p.m j : ℝ)^(-50 : ℝ) *
--             (1 + 4 * (p.m j : ℝ)^(-6 / 5 : ℝ) +
--               (p.m j : ℝ)^(-50 : ℝ))^(Fintype.card κ - 1))
--   ```
--
--   **Definitions.** The statement is written with `OAI.Invariant233.ProductScaleData` (definitions bundle `Q234IR000` of this split); `OAI.Invariant233.ProductSamplingPhaseMoments.mean`, `OAI.Invariant233.ProductSamplingPhaseMoments.realBVSize`, `OAI.Invariant233.ProductSamplingPhaseMoments.unitInterval` and `OAI.Invariant233.UniformIntervalPhase.lambdaLaw` (definitions bundle `Q234IR001` of this split); `OAI.Invariant233.ProductSamplingPowersAt`, `OAI.Invariant233.ProductScaleLaws` and `OAI.Invariant233.ProductScaleData.N` (definitions bundle `Q234IR003` of this split).
--
--   **Used by.** The proofs of `OAI.Invariant233.ProductModel.SamplingWeights.ae_all_sourceCylinder_energy_tendsto_zero` and `OAI.Invariant233.ProductModel.SamplingWeights.ae_all_source_univ_energy_tendsto_zero` of this split import it.
-- source:
--   OpenAI, Invariant-projection counterexamples for every irrational rotation, OpenAI Math Release, September 27, 2026, https://github.com/openai/math (result family 293; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Invariant-projection-counterexamples-for-every-irrational-rotation-September-27-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/IrrationalRotation/Sampling/ProductSamplingNumericalBudget.lean (declaration OAI.Invariant233.ProductSamplingPhaseMoments.expected_average_error_le_source_scale)

import Mathlib
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Polynomial.Degree.TrailingDegree
import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.Algebra.Polynomial.OfFn
import Mathlib.Analysis.BoundedVariation
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLogExp
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Int.Interval
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Group.AddCircle
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Probability.ConditionalProbability
import Mathlib.Tactic
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.EMetricSpace.BoundedVariation
import Definitions.Def_Q234IR003

section

attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set

namespace Invariant233.ProductSamplingPhaseMoments

theorem expected_average_error_le_source_scale {κ : Type*} [Fintype κ]
    {p : ProductScaleData} (hp : ProductScaleLaws p) {j : ℕ} (hm : 200 ≤ p.m j)
    (N₀ : κ → ℝ) (hN : ∀ i, 0 < N₀ i) (hNle : ∀ i, N₀ i ≤ p.N j)
    (powers : Finset ℕ) (hs : ProductSamplingPowersAt p j powers)
    (u : κ → ℝ → ℝ → ℝ) (C : κ → ℝ)
    (hu : ∀ i, Measurable (Function.uncurry (u i)))
    (hbound : ∀ i s t, |u i s t| ≤ C i)
    (hzero : ∀ i s t, 0 ≤ u i s t)
    (hmean : ∀ i s, mean (u i) s ≤ 2)
    (hBV : ∀ i s, s ∈ Ico (0 : ℝ) 1 → BoundedVariationOn (u i s) (Icc (0 : ℝ) 1))
    (hV : ∀ i s, s ∈ Ico (0 : ℝ) 1 → realBVSize (u i s) ≤ 16 * (p.m j : ℝ)^10)
    (hbase : ∀ i, (∫ s, (mean (u i) s)^2 ∂unitInterval) ≤
      1 + ((p.m j : ℝ)^(-(3 / 5 : ℝ)))^2 / (1 - (p.m j : ℝ)^(-(3 / 5 : ℝ)))^2)
    {D : ℝ}
    (hsquare : ∀ i, (∫ s, ∫ t, (u i s t)^2 ∂unitInterval ∂unitInterval) ≤ D) :
    (∫ a, ∫ x, ((powers.card : ℝ)⁻¹ *
        (∑ n ∈ powers, ∏ i, u i (x i) (Int.fract ((n : ℝ) * a i))) -
        ∏ i, mean (u i) (x i))^2
      ∂Measure.pi (fun _ : κ => unitInterval)
      ∂Measure.pi (fun i => UniformIntervalPhase.lambdaLaw (N₀ i))) ≤
      (2 * D)^Fintype.card κ / (powers.card : ℝ) +
        3 * ((Fintype.card κ : ℝ) * (p.m j : ℝ)^(-50 : ℝ) *
          (1 + 4 * (p.m j : ℝ)^(-6 / 5 : ℝ) +
            (p.m j : ℝ)^(-50 : ℝ))^(Fintype.card κ - 1)) := by
  sorry

end Invariant233.ProductSamplingPhaseMoments

end

end OAI
end
