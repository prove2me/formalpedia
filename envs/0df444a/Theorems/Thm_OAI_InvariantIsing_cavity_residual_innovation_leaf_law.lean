-- Prove2me | Theorems.Thm_OAI_InvariantIsing_cavity_residual_innovation_leaf_law
-- name    : OAI.InvariantIsing.cavity_residual_innovation_leaf_law
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T05:14:29.895074+00:00
-- url     : https://prove2.me/theorems/570f12e4-bc5a-4e77-80fa-5f3668118257
-- title:
--   OAI.InvariantIsing.cavity_residual_innovation_leaf_law: intermediate lemma from OpenAI, All-temperature pressure for orthogonally invariant Ising spin glasses
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.InvariantIsing.gaussianPattern_ground_limit_unconditional`, `OAI.InvariantIsing.gaussianPattern_norm_limits_unconditional`, `OAI.InvariantIsing.gaussianPattern_pressure_limit_unconditional`, `OAI.InvariantIsing.ground_state_limit_unconditional`, `OAI.InvariantIsing.limiting_pressure_of_extreme_limits_unconditional`, `OAI.InvariantIsing.limiting_wasserstein_field_pressure_of_extreme_limits_unconditional`, `OAI.InvariantIsing.positive_temperature_pressure_unconditional`, `OAI.InvariantIsing.random_field_pressure_tendsto_ae_unconditional`, `OAI.InvariantIsing.random_pressure_limit_unconditional`, `OAI.InvariantIsing.random_pressure_tendsto_ae_unconditional` and `OAI.InvariantIsing.random_pressure_tendsto_in_measure_unconditional`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *All-temperature pressure for orthogonally invariant Ising spin glasses*, OpenAI Math Release, September 25, 2026, result family 234, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.InvariantIsing.cavity_residual_innovation_leaf_law` of [lean/OAI/Probability/InvariantIsing/Cavity/CavityResidualInnovation.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/InvariantIsing/Cavity/CavityResidualInnovation.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.InvariantIsing`, with `open MeasureTheory ProbabilityTheory IsingPerceptron`, `open scoped RealInnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator ENNReal`):
--
--   ```lean
--   theorem cavity_residual_innovation_leaf_law {d : ℕ} (n : ℕ)
--       (K : Matrix (Fin d) (Fin d) ℝ) (H S : ℕ → Matrix (Fin d) (Fin d) ℝ) (b : ℕ → ℝ)
--       (hK : K.transpose = K) (hR : (H n).PosSemidef)
--       (hdet : IsUnit (1 - H n * K).det)
--       (hQ : (cavityFactorPrecision K (CFC.sqrt (H n))).PosDef)
--       (s : EuclideanSpace ℝ (Fin d)) (V : NoiseTree (EuclideanSpace ℝ (Fin d)) n)
--       (hZ : cavityResidualPartition n K (H n) s V < ∞)
--       (hV : NoiseGibbsRegular n b (cavityGaussianMarks S)
--         (fun i => cavityQuadraticStepWeight K (H i) (H (i + 1)) (b i))
--         (fun _ p => p.1 + p.2) s V) :
--       (cavityQuadraticResidualGibbs n K (H n) s V).map
--         (fun p => (cavityInnovationLeaf n
--           (fun i => cavityQuadraticStepWeight K (H i) (H (i + 1)) (b i))
--           (fun i => cavityStepInnovation K (H i) (H (i + 1))) s p.1,
--           cavityLeafSum n s p.1 + p.2 -
--             Matrix.toEuclideanCLM (𝕜 := ℝ) (1 - H n * K)⁻¹ (cavityLeafSum n s p.1))) =
--         (noiseLeafKernel (EuclideanSpace ℝ (Fin d)) n
--           (cavityInnovationTree n b (cavityGaussianMarks S)
--             (fun i => cavityQuadraticStepWeight K (H i) (H (i + 1)) (b i))
--             (fun i => cavityStepInnovation K (H i) (H (i + 1))) s V)).prod
--           (multivariateGaussian 0 (cavityResolvent K (H n)))
--   ```
--
--   **Definitions.** The statement is written with `OAI.InvariantIsing.cavityFactorPrecision`, `OAI.InvariantIsing.cavityGaussianMarks`, `OAI.InvariantIsing.cavityInnovationLeaf`, `OAI.InvariantIsing.cavityInnovationTree`, `OAI.InvariantIsing.cavityLeafSum`, `OAI.InvariantIsing.cavityQuadraticResidualGibbs`, `OAI.InvariantIsing.cavityQuadraticStepWeight`, `OAI.InvariantIsing.cavityResidualPartition`, `OAI.InvariantIsing.cavityResolvent` and `OAI.InvariantIsing.cavityStepInnovation` (definitions bundle `OAIQ258001` of this split); `OAI.IsingPerceptron.NoiseGibbsRegular`, `OAI.IsingPerceptron.NoiseLeaf`, `OAI.IsingPerceptron.NoiseTree`, `OAI.IsingPerceptron.noiseLeafKernel`, `OAI.IsingPerceptron.noiseLeafMeasurableSpace` and `OAI.IsingPerceptron.noiseTreeMeasurableSpace` (definitions bundle `OAIQ4Ip000` of this split).
--
--   **Used by.** The proofs of `OAI.InvariantIsing.cavity_full_log_evaluation`, `OAI.InvariantIsing.cavity_quadratic_one_transport`, `OAI.InvariantIsing.cavity_rooted_depth_test_transport`, `OAI.InvariantIsing.cavity_rooted_spin_depth_test_transport` and `OAI.InvariantIsing.prior_cavity_full_log_evaluation` of this split import it.
-- source:
--   OpenAI, All-temperature pressure for orthogonally invariant Ising spin glasses, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 234; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/All-temperature-pressure-for-orthogonally-invariant-Ising-spin-glasses-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/InvariantIsing/Cavity/CavityResidualInnovation.lean (declaration OAI.InvariantIsing.cavity_residual_innovation_leaf_law)

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

attribute [-instance] _root_.OAI.InvariantIsing.cavityRootedPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualBaseKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualKernel_markov _root_.OAI.InvariantIsing.rootedResidualPrior_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped RealInnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator ENNReal

namespace InvariantIsing

theorem cavity_residual_innovation_leaf_law {d : ℕ} (n : ℕ)
    (K : Matrix (Fin d) (Fin d) ℝ) (H S : ℕ → Matrix (Fin d) (Fin d) ℝ) (b : ℕ → ℝ)
    (hK : K.transpose = K) (hR : (H n).PosSemidef)
    (hdet : IsUnit (1 - H n * K).det)
    (hQ : (cavityFactorPrecision K (CFC.sqrt (H n))).PosDef)
    (s : EuclideanSpace ℝ (Fin d)) (V : NoiseTree (EuclideanSpace ℝ (Fin d)) n)
    (hZ : cavityResidualPartition n K (H n) s V < ∞)
    (hV : NoiseGibbsRegular n b (cavityGaussianMarks S)
      (fun i => cavityQuadraticStepWeight K (H i) (H (i + 1)) (b i))
      (fun _ p => p.1 + p.2) s V) :
    (cavityQuadraticResidualGibbs n K (H n) s V).map
      (fun p => (cavityInnovationLeaf n
        (fun i => cavityQuadraticStepWeight K (H i) (H (i + 1)) (b i))
        (fun i => cavityStepInnovation K (H i) (H (i + 1))) s p.1,
        cavityLeafSum n s p.1 + p.2 -
          Matrix.toEuclideanCLM (𝕜 := ℝ) (1 - H n * K)⁻¹ (cavityLeafSum n s p.1))) =
      (noiseLeafKernel (EuclideanSpace ℝ (Fin d)) n
        (cavityInnovationTree n b (cavityGaussianMarks S)
          (fun i => cavityQuadraticStepWeight K (H i) (H (i + 1)) (b i))
          (fun i => cavityStepInnovation K (H i) (H (i + 1))) s V)).prod
        (multivariateGaussian 0 (cavityResolvent K (H n))) := by
  sorry

end InvariantIsing

end

end OAI
end
