-- Prove2me | Theorems.Thm_OAI_InvariantIsing_field_vector_log_root_integral
-- name    : OAI.InvariantIsing.field_vector_log_root_integral
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T05:38:30.047895+00:00
-- url     : https://prove2.me/theorems/e94f3e22-50e4-4da4-bd8a-ede676e1b061
-- title:
--   OAI.InvariantIsing.field_vector_log_root_integral: intermediate lemma from OpenAI, All-temperature pressure for orthogonally invariant Ising spin glasses
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.InvariantIsing.gaussianPattern_ground_limit_unconditional`, `OAI.InvariantIsing.gaussianPattern_norm_limits_unconditional`, `OAI.InvariantIsing.gaussianPattern_pressure_limit_unconditional`, `OAI.InvariantIsing.ground_state_limit_unconditional`, `OAI.InvariantIsing.limiting_pressure_of_extreme_limits_unconditional`, `OAI.InvariantIsing.limiting_wasserstein_field_pressure_of_extreme_limits_unconditional`, `OAI.InvariantIsing.positive_temperature_pressure_unconditional`, `OAI.InvariantIsing.random_field_pressure_tendsto_ae_unconditional`, `OAI.InvariantIsing.random_pressure_limit_unconditional`, `OAI.InvariantIsing.random_pressure_tendsto_ae_unconditional` and `OAI.InvariantIsing.random_pressure_tendsto_in_measure_unconditional`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *All-temperature pressure for orthogonally invariant Ising spin glasses*, OpenAI Math Release, September 25, 2026, result family 234, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.InvariantIsing.field_vector_log_root_integral` of [lean/OAI/Probability/InvariantIsing/Fields/FieldLogNormalizer.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/InvariantIsing/Fields/FieldLogNormalizer.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.InvariantIsing`, with `open MeasureTheory ProbabilityTheory IsingPerceptron`, `open scoped BigOperators NNReal`):
--
--   ```lean
--   theorem field_vector_log_root_integral (N : ℕ) (hN : 0 < N) (h : FieldStep)
--       (root : ℝ≥0) :
--       Integrable (fun p => fieldVectorLogNormalizer N h p.1 p.2)
--         ((vectorGaussianLaw N root : Measure (Fin N → ℝ)).prod (fieldVectorCoordinateLaw N h)) ∧
--         (∫ p, fieldVectorLogNormalizer N h p.1 p.2
--           ∂(vectorGaussianLaw N root : Measure (Fin N → ℝ)).prod (fieldVectorCoordinateLaw N h)) =
--         ∫ z, cascadeRecursion h.depth (chainExponent h.cut)
--           (fun i => vectorGaussianLaw N (fieldStepVariance h i))
--           (fun _ p => p.1 + p.2) (fun y => ∑ i, Real.log (Real.cosh (y i))) z
--           ∂(vectorGaussianLaw N root : Measure (Fin N → ℝ))
--   ```
--
--   **Definitions.** The statement is written with `OAI.InvariantIsing.vectorGaussianLaw` (definitions bundle `OAIQ258001` of this split); `OAI.InvariantIsing.fieldStepVariance` and `OAI.InvariantIsing.fieldVectorCoordinateLaw` (definitions bundle `OAIQ258003` of this split); `OAI.InvariantIsing.fieldVectorLogNormalizer` (definitions bundle `OAIQ258005` of this split); `OAI.IsingPerceptron.ForestVertex`, `OAI.IsingPerceptron.LabeledTree`, `OAI.IsingPerceptron.cascadeRecursion`, `OAI.IsingPerceptron.chainExponent` and `OAI.IsingPerceptron.labeledTreeMeasurableSpace` (definitions bundle `OAIQ4Ip000` of this split); `OAI.InvariantIsing.FieldStep` (the published bundle `Def_InvariantIsing`).
--
--   **Used by.** The proofs of `OAI.InvariantIsing.cavity_finite_log_evaluation`, `OAI.InvariantIsing.cavity_linear_rooted_log_integral` and `OAI.InvariantIsing.field_vector_log_mean` of this split import it.
-- source:
--   OpenAI, All-temperature pressure for orthogonally invariant Ising spin glasses, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 234; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/All-temperature-pressure-for-orthogonally-invariant-Ising-spin-glasses-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/InvariantIsing/Fields/FieldLogNormalizer.lean (declaration OAI.InvariantIsing.field_vector_log_root_integral)

import Mathlib
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Moments.ComplexMGF
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.StrongLaw
import Definitions.Def_InvariantIsing
import Definitions.Def_OAIQ258005

section

attribute [-instance] _root_.OAI.InvariantIsing.biasedFieldLevelSpinPair_probability _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldCanonicalEndpointLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalSpinLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalVectorLaw_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators NNReal

namespace InvariantIsing

theorem field_vector_log_root_integral (N : ℕ) (hN : 0 < N) (h : FieldStep)
    (root : ℝ≥0) :
    Integrable (fun p => fieldVectorLogNormalizer N h p.1 p.2)
      ((vectorGaussianLaw N root : Measure (Fin N → ℝ)).prod (fieldVectorCoordinateLaw N h)) ∧
      (∫ p, fieldVectorLogNormalizer N h p.1 p.2
        ∂(vectorGaussianLaw N root : Measure (Fin N → ℝ)).prod (fieldVectorCoordinateLaw N h)) =
      ∫ z, cascadeRecursion h.depth (chainExponent h.cut)
        (fun i => vectorGaussianLaw N (fieldStepVariance h i))
        (fun _ p => p.1 + p.2) (fun y => ∑ i, Real.log (Real.cosh (y i))) z
        ∂(vectorGaussianLaw N root : Measure (Fin N → ℝ)) := by
  sorry

end InvariantIsing

end

end OAI
end
