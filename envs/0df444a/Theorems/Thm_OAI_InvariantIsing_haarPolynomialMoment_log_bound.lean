-- Prove2me | Theorems.Thm_OAI_InvariantIsing_haarPolynomialMoment_log_bound
-- name    : OAI.InvariantIsing.haarPolynomialMoment_log_bound
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-12T05:38:49.555237+00:00
-- url     : https://prove2.me/theorems/71380e97-4cb5-4fd3-b84a-2f98e725a525
-- title:
--   OAI.InvariantIsing.haarPolynomialMoment_log_bound: intermediate lemma from OpenAI, All-temperature pressure for orthogonally invariant Ising spin glasses
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.InvariantIsing.gaussianPattern_ground_limit_unconditional`, `OAI.InvariantIsing.gaussianPattern_norm_limits_unconditional`, `OAI.InvariantIsing.gaussianPattern_pressure_limit_unconditional`, `OAI.InvariantIsing.ground_state_limit_unconditional`, `OAI.InvariantIsing.limiting_pressure_of_extreme_limits_unconditional`, `OAI.InvariantIsing.limiting_wasserstein_field_pressure_of_extreme_limits_unconditional`, `OAI.InvariantIsing.positive_temperature_pressure_unconditional`, `OAI.InvariantIsing.random_field_pressure_tendsto_ae_unconditional`, `OAI.InvariantIsing.random_pressure_limit_unconditional`, `OAI.InvariantIsing.random_pressure_tendsto_ae_unconditional` and `OAI.InvariantIsing.random_pressure_tendsto_in_measure_unconditional`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *All-temperature pressure for orthogonally invariant Ising spin glasses*, OpenAI Math Release, September 25, 2026, result family 234, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.InvariantIsing.haarPolynomialMoment_log_bound` of [lean/OAI/Probability/InvariantIsing/Haar/HaarPolynomialMomentShift.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/InvariantIsing/Haar/HaarPolynomialMomentShift.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.InvariantIsing`, with `open Matrix MvPolynomial MeasureTheory`):
--
--   ```lean
--   theorem haarPolynomialMoment_log_bound {N : ℕ} (hN : 3 ≤ N)
--       (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant]
--       (p : MatrixPolynomial N) (C : ℝ) (hC : 0 ≤ C)
--       (hG : ∀ U : SpecialOrthogonal N, haarPolynomialValue (haarPolynomialGamma p p) U ≤ C)
--       {t : ℝ} (ht : 0 < t) :
--       Real.log (haarPolynomialMoment μ p t) ≤
--         (∫ U, haarPolynomialValue p U ∂μ)*t+C/(2*((N:ℝ)-2))*t^2
--   ```
--
--   **Definitions.** The statement is written with `Matrix.compatMeasurableSpace` (definitions bundle `OAIQ258000` of this split); `OAI.InvariantIsing.MatrixPolynomial` and `OAI.InvariantIsing.SpecialOrthogonal` (definitions bundle `OAIQ258001` of this split); `OAI.InvariantIsing.haarPolynomialValue` (definitions bundle `OAIQ258003` of this split); `OAI.InvariantIsing.haarPolynomialGamma` (definitions bundle `OAIQ258004` of this split); `OAI.InvariantIsing.haarPolynomialMoment` (definitions bundle `OAIQ258005` of this split).
--
--   **Used by.** The proofs of `OAI.InvariantIsing.gaussianPattern_ground_limit_unconditional`, `OAI.InvariantIsing.gaussianPattern_norm_limits_unconditional`, `OAI.InvariantIsing.gaussianPattern_pressure_limit_unconditional`, `OAI.InvariantIsing.ground_state_limit_unconditional`, `OAI.InvariantIsing.limiting_pressure_of_extreme_limits_unconditional`, `OAI.InvariantIsing.limiting_wasserstein_field_pressure_of_extreme_limits_unconditional`, `OAI.InvariantIsing.positive_temperature_pressure_unconditional`, `OAI.InvariantIsing.random_field_pressure_tendsto_ae_unconditional`, `OAI.InvariantIsing.random_pressure_limit_unconditional`, `OAI.InvariantIsing.random_pressure_tendsto_ae_unconditional` and `OAI.InvariantIsing.random_pressure_tendsto_in_measure_unconditional` of this split import it.
-- source:
--   OpenAI, All-temperature pressure for orthogonally invariant Ising spin glasses, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 234; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/All-temperature-pressure-for-orthogonally-invariant-Ising-spin-glasses-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/InvariantIsing/Haar/HaarPolynomialMomentShift.lean (declaration OAI.InvariantIsing.haarPolynomialMoment_log_bound)

import Mathlib
import Mathlib.Algebra.MvPolynomial.Derivation
import Mathlib.Analysis.Calculus.LHopital
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Data.List.Induction
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Moments.Variance
import Mathlib.RingTheory.Derivation.Lie
import Mathlib.Topology.Order.Compact
import Definitions.Def_OAIQ258005

section

attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.tensorFrozenLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Matrix MvPolynomial MeasureTheory
namespace InvariantIsing

theorem haarPolynomialMoment_log_bound {N : ℕ} (hN : 3 ≤ N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant]
    (p : MatrixPolynomial N) (C : ℝ) (hC : 0 ≤ C)
    (hG : ∀ U : SpecialOrthogonal N, haarPolynomialValue (haarPolynomialGamma p p) U ≤ C)
    {t : ℝ} (ht : 0 < t) :
    Real.log (haarPolynomialMoment μ p t) ≤
      (∫ U, haarPolynomialValue p U ∂μ)*t+C/(2*((N:ℝ)-2))*t^2 := by
  sorry

end InvariantIsing

end

end OAI
end
