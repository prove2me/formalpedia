-- Prove2me | Theorems.Thm_OAI_InvariantIsing_cavity_residual_partition_log_integral
-- name    : OAI.InvariantIsing.cavity_residual_partition_log_integral
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T05:15:12.835931+00:00
-- url     : https://prove2.me/theorems/5572f34e-ade8-457b-b489-8dfefe162f5c
-- title:
--   OAI.InvariantIsing.cavity_residual_partition_log_integral: intermediate lemma from OpenAI, All-temperature pressure for orthogonally invariant Ising spin glasses
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.InvariantIsing.gaussianPattern_ground_limit_unconditional`, `OAI.InvariantIsing.gaussianPattern_norm_limits_unconditional`, `OAI.InvariantIsing.gaussianPattern_pressure_limit_unconditional`, `OAI.InvariantIsing.ground_state_limit_unconditional`, `OAI.InvariantIsing.limiting_pressure_of_extreme_limits_unconditional`, `OAI.InvariantIsing.limiting_wasserstein_field_pressure_of_extreme_limits_unconditional`, `OAI.InvariantIsing.positive_temperature_pressure_unconditional`, `OAI.InvariantIsing.random_field_pressure_tendsto_ae_unconditional`, `OAI.InvariantIsing.random_pressure_limit_unconditional`, `OAI.InvariantIsing.random_pressure_tendsto_ae_unconditional` and `OAI.InvariantIsing.random_pressure_tendsto_in_measure_unconditional`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *All-temperature pressure for orthogonally invariant Ising spin glasses*, OpenAI Math Release, September 25, 2026, result family 234, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.InvariantIsing.cavity_residual_partition_log_integral` of [lean/OAI/Probability/InvariantIsing/Cavity/CavityResidualPartition.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/InvariantIsing/Cavity/CavityResidualPartition.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.InvariantIsing`, with `open MeasureTheory ProbabilityTheory IsingPerceptron`, `open scoped RealInnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator ENNReal`):
--
--   ```lean
--   theorem cavity_residual_partition_log_integral {d : ℕ} (n : ℕ)
--       (K : Matrix (Fin d) (Fin d) ℝ)
--       (H S : ℕ → Matrix (Fin d) (Fin d) ℝ) (b : ℕ → ℝ)
--       (S₀ : Matrix (Fin d) (Fin d) ℝ) (hS₀ : S₀.PosSemidef)
--       (hbCascade : CascadeExponents n b)
--       (hK : K.transpose = K) (hH : ∀ i, (H i).transpose = H i)
--       (hS : ∀ i, (S i).PosSemidef) (hb : ∀ i, 0 < b i)
--       (hdet : ∀ i, IsUnit (1 - H i * K).det)
--       (hΔ : ∀ i, H i - H (i + 1) = b i • S i)
--       (hQ : ∀ i, (cavityFactorPrecision
--         (b i • cavityBackwardQuadratic K (H (i + 1))) (CFC.sqrt (S i))).PosDef)
--       (hR : (H n).PosSemidef)
--       (hQR : (cavityFactorPrecision K (CFC.sqrt (H n))).PosDef) :
--       let P := (noiseCascadeLaw (EuclideanSpace ℝ (Fin d)) n b (cavityGaussianMarks S) : Measure _)
--       let Z := fun p : EuclideanSpace ℝ (Fin d) × NoiseTree (EuclideanSpace ℝ (Fin d)) n =>
--         Real.log (cavityResidualPartition n K (H n) p.1 p.2).toReal
--       Integrable Z ((multivariateGaussian 0 S₀).prod P) ∧
--         (∫ p, Z p ∂(multivariateGaussian 0 S₀).prod P) =
--           Matrix.trace (S₀ * cavityBackwardQuadratic K (H 0)) / 2 -
--             (∑ j ∈ Finset.range n, cavityDeterminantStep K H b j) -
--               Real.log (1 - H n * K).det / 2
--   ```
--
--   **Definitions.** The statement is written with `OAI.InvariantIsing.cavityBackwardQuadratic`, `OAI.InvariantIsing.cavityDeterminantStep`, `OAI.InvariantIsing.cavityFactorPrecision`, `OAI.InvariantIsing.cavityGaussianMarks` and `OAI.InvariantIsing.cavityResidualPartition` (definitions bundle `OAIQ258001` of this split); `OAI.IsingPerceptron.CascadeExponents`, `OAI.IsingPerceptron.NoiseTree`, `OAI.IsingPerceptron.noiseCascadeLaw` and `OAI.IsingPerceptron.noiseTreeMeasurableSpace` (definitions bundle `OAIQ4Ip000` of this split).
--
--   **Used by.** The proofs of `OAI.InvariantIsing.cavity_full_log_evaluation` and `OAI.InvariantIsing.prior_cavity_full_log_evaluation` of this split import it.
-- source:
--   OpenAI, All-temperature pressure for orthogonally invariant Ising spin glasses, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 234; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/All-temperature-pressure-for-orthogonally-invariant-Ising-spin-glasses-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/InvariantIsing/Cavity/CavityResidualPartition.lean (declaration OAI.InvariantIsing.cavity_residual_partition_log_integral)

import Mathlib
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Moments.ComplexMGF
import Mathlib.Probability.StrongLaw
import Definitions.Def_OAIQ258001

section

attribute [-instance] _root_.OAI.InvariantIsing.cavityQuadraticResidualGibbs_probability _root_.OAI.InvariantIsing.cavityRootedPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualBaseKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualKernel_markov _root_.OAI.InvariantIsing.rootedResidualPrior_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped RealInnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator ENNReal

namespace InvariantIsing

theorem cavity_residual_partition_log_integral {d : ℕ} (n : ℕ)
    (K : Matrix (Fin d) (Fin d) ℝ)
    (H S : ℕ → Matrix (Fin d) (Fin d) ℝ) (b : ℕ → ℝ)
    (S₀ : Matrix (Fin d) (Fin d) ℝ) (hS₀ : S₀.PosSemidef)
    (hbCascade : CascadeExponents n b)
    (hK : K.transpose = K) (hH : ∀ i, (H i).transpose = H i)
    (hS : ∀ i, (S i).PosSemidef) (hb : ∀ i, 0 < b i)
    (hdet : ∀ i, IsUnit (1 - H i * K).det)
    (hΔ : ∀ i, H i - H (i + 1) = b i • S i)
    (hQ : ∀ i, (cavityFactorPrecision
      (b i • cavityBackwardQuadratic K (H (i + 1))) (CFC.sqrt (S i))).PosDef)
    (hR : (H n).PosSemidef)
    (hQR : (cavityFactorPrecision K (CFC.sqrt (H n))).PosDef) :
    let P := (noiseCascadeLaw (EuclideanSpace ℝ (Fin d)) n b (cavityGaussianMarks S) : Measure _)
    let Z := fun p : EuclideanSpace ℝ (Fin d) × NoiseTree (EuclideanSpace ℝ (Fin d)) n =>
      Real.log (cavityResidualPartition n K (H n) p.1 p.2).toReal
    Integrable Z ((multivariateGaussian 0 S₀).prod P) ∧
      (∫ p, Z p ∂(multivariateGaussian 0 S₀).prod P) =
        Matrix.trace (S₀ * cavityBackwardQuadratic K (H 0)) / 2 -
          (∑ j ∈ Finset.range n, cavityDeterminantStep K H b j) -
            Real.log (1 - H n * K).det / 2 := by
  sorry

end InvariantIsing

end

end OAI
end
