-- Prove2me | Theorems.Thm_OAI_InvariantIsing_cavity_residual_partition_pos_finite
-- name    : OAI.InvariantIsing.cavity_residual_partition_pos_finite
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T05:14:43.498234+00:00
-- url     : https://prove2.me/theorems/8910c468-f79d-4da2-b233-96d49f392f52
-- title:
--   OAI.InvariantIsing.cavity_residual_partition_pos_finite: intermediate lemma from OpenAI, All-temperature pressure for orthogonally invariant Ising spin glasses
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.InvariantIsing.gaussianPattern_ground_limit_unconditional`, `OAI.InvariantIsing.gaussianPattern_norm_limits_unconditional`, `OAI.InvariantIsing.gaussianPattern_pressure_limit_unconditional`, `OAI.InvariantIsing.ground_state_limit_unconditional`, `OAI.InvariantIsing.limiting_pressure_of_extreme_limits_unconditional`, `OAI.InvariantIsing.limiting_wasserstein_field_pressure_of_extreme_limits_unconditional`, `OAI.InvariantIsing.positive_temperature_pressure_unconditional`, `OAI.InvariantIsing.random_field_pressure_tendsto_ae_unconditional`, `OAI.InvariantIsing.random_pressure_limit_unconditional`, `OAI.InvariantIsing.random_pressure_tendsto_ae_unconditional` and `OAI.InvariantIsing.random_pressure_tendsto_in_measure_unconditional`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *All-temperature pressure for orthogonally invariant Ising spin glasses*, OpenAI Math Release, September 25, 2026, result family 234, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.InvariantIsing.cavity_residual_partition_pos_finite` of [lean/OAI/Probability/InvariantIsing/Cavity/CavityResidualFinite.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/InvariantIsing/Cavity/CavityResidualFinite.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.InvariantIsing`, with `open MeasureTheory ProbabilityTheory IsingPerceptron`, `open scoped RealInnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator ENNReal`):
--
--   ```lean
--   theorem cavity_residual_partition_pos_finite {d : ℕ} (n : ℕ)
--       (K : Matrix (Fin d) (Fin d) ℝ)
--       (H S : ℕ → Matrix (Fin d) (Fin d) ℝ) (b : ℕ → ℝ)
--       (hbCascade : CascadeExponents n b)
--       (hK : K.transpose = K) (hH : ∀ i, (H i).transpose = H i)
--       (hS : ∀ i, (S i).PosSemidef) (hb : ∀ i, 0 < b i)
--       (hdet : ∀ i, IsUnit (1 - H i * K).det)
--       (hΔ : ∀ i, H i - H (i + 1) = b i • S i)
--       (hQ : ∀ i, (cavityFactorPrecision
--         (b i • cavityBackwardQuadratic K (H (i + 1))) (CFC.sqrt (S i))).PosDef)
--       (hR : (H n).PosSemidef)
--       (hQR : (cavityFactorPrecision K (CFC.sqrt (H n))).PosDef)
--       (s : EuclideanSpace ℝ (Fin d)) :
--       ∀ᵐ V ∂(noiseCascadeLaw (EuclideanSpace ℝ (Fin d)) n b (cavityGaussianMarks S) : Measure _),
--         0 < cavityResidualPartition n K (H n) s V ∧
--           cavityResidualPartition n K (H n) s V < ∞
--   ```
--
--   **Definitions.** The statement is written with `OAI.InvariantIsing.cavityBackwardQuadratic`, `OAI.InvariantIsing.cavityFactorPrecision`, `OAI.InvariantIsing.cavityGaussianMarks` and `OAI.InvariantIsing.cavityResidualPartition` (definitions bundle `OAIQ258001` of this split); `OAI.IsingPerceptron.CascadeExponents`, `OAI.IsingPerceptron.NoiseTree`, `OAI.IsingPerceptron.noiseCascadeLaw` and `OAI.IsingPerceptron.noiseTreeMeasurableSpace` (definitions bundle `OAIQ4Ip000` of this split).
--
--   **Used by.** The proofs of `OAI.InvariantIsing.cavity_finite_labeled_moment`, `OAI.InvariantIsing.cavity_finite_original_integrability`, `OAI.InvariantIsing.cavity_full_log_evaluation`, `OAI.InvariantIsing.cavity_quadratic_one_transport`, `OAI.InvariantIsing.cavity_rooted_depth_test_transport`, `OAI.InvariantIsing.cavity_rooted_spin_depth_test_transport` and `OAI.InvariantIsing.prior_cavity_full_log_evaluation` of this split import it.
-- source:
--   OpenAI, All-temperature pressure for orthogonally invariant Ising spin glasses, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 234; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/All-temperature-pressure-for-orthogonally-invariant-Ising-spin-glasses-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/InvariantIsing/Cavity/CavityResidualFinite.lean (declaration OAI.InvariantIsing.cavity_residual_partition_pos_finite)

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

theorem cavity_residual_partition_pos_finite {d : ℕ} (n : ℕ)
    (K : Matrix (Fin d) (Fin d) ℝ)
    (H S : ℕ → Matrix (Fin d) (Fin d) ℝ) (b : ℕ → ℝ)
    (hbCascade : CascadeExponents n b)
    (hK : K.transpose = K) (hH : ∀ i, (H i).transpose = H i)
    (hS : ∀ i, (S i).PosSemidef) (hb : ∀ i, 0 < b i)
    (hdet : ∀ i, IsUnit (1 - H i * K).det)
    (hΔ : ∀ i, H i - H (i + 1) = b i • S i)
    (hQ : ∀ i, (cavityFactorPrecision
      (b i • cavityBackwardQuadratic K (H (i + 1))) (CFC.sqrt (S i))).PosDef)
    (hR : (H n).PosSemidef)
    (hQR : (cavityFactorPrecision K (CFC.sqrt (H n))).PosDef)
    (s : EuclideanSpace ℝ (Fin d)) :
    ∀ᵐ V ∂(noiseCascadeLaw (EuclideanSpace ℝ (Fin d)) n b (cavityGaussianMarks S) : Measure _),
      0 < cavityResidualPartition n K (H n) s V ∧
        cavityResidualPartition n K (H n) s V < ∞ := by
  sorry

end InvariantIsing

end

end OAI
end
