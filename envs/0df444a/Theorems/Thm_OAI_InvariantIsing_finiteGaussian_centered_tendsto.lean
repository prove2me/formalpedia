-- Prove2me | Theorems.Thm_OAI_InvariantIsing_finiteGaussian_centered_tendsto
-- name    : OAI.InvariantIsing.finiteGaussian_centered_tendsto
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T05:09:47.283217+00:00
-- url     : https://prove2.me/theorems/10d95b77-dd01-49d9-a4e3-9dc3cc1061a5
-- title:
--   OAI.InvariantIsing.finiteGaussian_centered_tendsto: intermediate lemma from OpenAI, All-temperature pressure for orthogonally invariant Ising spin glasses
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.InvariantIsing.gaussianPattern_ground_limit_unconditional`, `OAI.InvariantIsing.gaussianPattern_norm_limits_unconditional`, `OAI.InvariantIsing.gaussianPattern_pressure_limit_unconditional`, `OAI.InvariantIsing.ground_state_limit_unconditional`, `OAI.InvariantIsing.limiting_pressure_of_extreme_limits_unconditional`, `OAI.InvariantIsing.limiting_wasserstein_field_pressure_of_extreme_limits_unconditional`, `OAI.InvariantIsing.positive_temperature_pressure_unconditional`, `OAI.InvariantIsing.random_field_pressure_tendsto_ae_unconditional`, `OAI.InvariantIsing.random_pressure_limit_unconditional`, `OAI.InvariantIsing.random_pressure_tendsto_ae_unconditional` and `OAI.InvariantIsing.random_pressure_tendsto_in_measure_unconditional`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *All-temperature pressure for orthogonally invariant Ising spin glasses*, OpenAI Math Release, September 25, 2026, result family 234, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.InvariantIsing.finiteGaussian_centered_tendsto` of [lean/OAI/Probability/InvariantIsing/Gaussian/GaussianSingularFluctuation.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/InvariantIsing/Gaussian/GaussianSingularFluctuation.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.InvariantIsing`, with `open MeasureTheory ProbabilityTheory Filter Set`, `open scoped NNReal ENNReal Topology`):
--
--   ```lean
--   theorem finiteGaussian_centered_tendsto {ι : ℕ → Type*} [∀ k, Fintype (ι k)]
--       (f : (k : ℕ) → EuclideanSpace ℝ (ι k) → ℝ) (hf : ∀ k, LipschitzWith 1 (f k))
--       {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
--       (Z : (k : ℕ) → Ω → EuclideanSpace ℝ (ι k))
--       (hZ : ∀ k, HasLaw (Z k) (stdGaussian _) P) :
--       TendstoInMeasure P (fun k ω =>
--         (f k (Z k ω)-(∫ x, f k x ∂stdGaussian _))/Real.sqrt (k+1)) atTop (fun _ => 0)
--   ```
--
--   **Used by.** The proofs of `OAI.InvariantIsing.gaussianPatternSingularMax_upper_edge` and `OAI.InvariantIsing.gaussianPatternTranspose_lower_edge` of this split import it.
-- source:
--   OpenAI, All-temperature pressure for orthogonally invariant Ising spin glasses, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 234; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/All-temperature-pressure-for-orthogonally-invariant-Ising-spin-glasses-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/InvariantIsing/Gaussian/GaussianSingularFluctuation.lean (declaration OAI.InvariantIsing.finiteGaussian_centered_tendsto)

import Mathlib
import Mathlib.Algebra.Group.Pointwise.Set.Scalar
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.AffineMap
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.Probability.Distributions.Gaussian.Fernique
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.StrongLaw
import Mathlib.Tactic
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Order.Compact

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
namespace InvariantIsing

theorem finiteGaussian_centered_tendsto {ι : ℕ → Type*} [∀ k, Fintype (ι k)]
    (f : (k : ℕ) → EuclideanSpace ℝ (ι k) → ℝ) (hf : ∀ k, LipschitzWith 1 (f k))
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Z : (k : ℕ) → Ω → EuclideanSpace ℝ (ι k))
    (hZ : ∀ k, HasLaw (Z k) (stdGaussian _) P) :
    TendstoInMeasure P (fun k ω =>
      (f k (Z k ω)-(∫ x, f k x ∂stdGaussian _))/Real.sqrt (k+1)) atTop (fun _ => 0) := by
  sorry

end InvariantIsing

end

end OAI
end
