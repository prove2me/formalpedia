-- Prove2me | Theorems.Thm_OAI_InvariantIsing_spinPriorLabeledLog_conditional
-- name    : OAI.InvariantIsing.spinPriorLabeledLog_conditional
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-12T05:58:15.47447+00:00
-- url     : https://prove2.me/theorems/5156d616-2406-4e41-94bf-c98b8d6f057a
-- title:
--   OAI.InvariantIsing.spinPriorLabeledLog_conditional: intermediate lemma from OpenAI, All-temperature pressure for orthogonally invariant Ising spin glasses
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.InvariantIsing.gaussianPattern_ground_limit_unconditional`, `OAI.InvariantIsing.gaussianPattern_norm_limits_unconditional`, `OAI.InvariantIsing.gaussianPattern_pressure_limit_unconditional`, `OAI.InvariantIsing.ground_state_limit_unconditional`, `OAI.InvariantIsing.limiting_pressure_of_extreme_limits_unconditional`, `OAI.InvariantIsing.limiting_wasserstein_field_pressure_of_extreme_limits_unconditional`, `OAI.InvariantIsing.positive_temperature_pressure_unconditional`, `OAI.InvariantIsing.random_field_pressure_tendsto_ae_unconditional`, `OAI.InvariantIsing.random_pressure_limit_unconditional`, `OAI.InvariantIsing.random_pressure_tendsto_ae_unconditional` and `OAI.InvariantIsing.random_pressure_tendsto_in_measure_unconditional`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *All-temperature pressure for orthogonally invariant Ising spin glasses*, OpenAI Math Release, September 25, 2026, result family 234, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.InvariantIsing.spinPriorLabeledLog_conditional` of [lean/OAI/Probability/InvariantIsing/Fields/SpinPriorLabeledMoments.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/InvariantIsing/Fields/SpinPriorLabeledMoments.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.InvariantIsing`, with `open MeasureTheory ProbabilityTheory IsingPerceptron`, `open scoped BigOperators NNReal`):
--
--   ```lean
--   theorem spinPriorLabeledLog_conditional {N m k : ℕ} (hN : 0 < N)
--       (π : Measure (Spin N)) [IsProbabilityMeasure π]
--       (eig : Fin N → ℝ) (U : Rotation N) (c : Fin N → ℝ)
--       (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amp : Fin k → ℝ)
--       (n : ℕ) (b : ℕ → ℝ) (v : ℕ → SpinTensorIndex I degree → ℝ≥0)
--       (hb : CascadeExponents n b) (z : SpinTensorIndex I degree → ℝ) :
--       let P := tensorLabeledLaw U I degree amp n b v
--       let F := spinPriorLabeledLog π eig U c I degree amp n z
--       let X := spinPriorCascadeValue π eig U c I degree amp n b v z
--       Integrable F P ∧ (∫ p, F p ∂P) = X ∧
--         Integrable (fun p => (F p-X)^2) P ∧
--         (∫ p, (F p-X)^2 ∂P) ≤
--           4 * ∫ T, (Real.log (rawTreeTotal n T).toReal)^2
--             ∂(rawCascadeLaw n b : Measure (RawTree n))
--   ```
--
--   **Definitions.** The statement is written with `OAI.InvariantIsing.SpinTensorIndex` (definitions bundle `OAIQ258000` of this split); `OAI.InvariantIsing.TensorLabeledData` (definitions bundle `OAIQ258003` of this split); `OAI.InvariantIsing.spinPriorCascadeValue`, `OAI.InvariantIsing.spinPriorLabeledLog` and `OAI.InvariantIsing.tensorLabeledLaw` (definitions bundle `OAIQ258005` of this split); `OAI.IsingPerceptron.CascadeExponents`, `OAI.IsingPerceptron.ForestVertex`, `OAI.IsingPerceptron.LabeledTree`, `OAI.IsingPerceptron.RawTree`, `OAI.IsingPerceptron.labeledTreeMeasurableSpace`, `OAI.IsingPerceptron.rawCascadeLaw`, `OAI.IsingPerceptron.rawTreeMeasurableSpace` and `OAI.IsingPerceptron.rawTreeTotal` (definitions bundle `OAIQ4Ip000` of this split); `OAI.InvariantIsing.Rotation` and `OAI.InvariantIsing.Spin` (the published bundle `Def_InvariantIsing`).
--
--   **Used by.** The proofs of `OAI.InvariantIsing.spinPriorMeanPressure_field` and `OAI.InvariantIsing.spinPriorProfileLog_variance` of this split import it.
-- source:
--   OpenAI, All-temperature pressure for orthogonally invariant Ising spin glasses, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 234; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/All-temperature-pressure-for-orthogonally-invariant-Ising-spin-glasses-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/InvariantIsing/Fields/SpinPriorLabeledMoments.lean (declaration OAI.InvariantIsing.spinPriorLabeledLog_conditional)

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

attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityQuadraticResidualGibbs_probability _root_.OAI.InvariantIsing.cavityQuadraticResidualKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRootedPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualBaseKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualKernel_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorRootTreeLaw_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability _root_.OAI.InvariantIsing.vectorTerminalNoiseLaw_probability _root_.OAI.InvariantIsing.rootedResidualPrior_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators NNReal
namespace InvariantIsing

theorem spinPriorLabeledLog_conditional {N m k : ℕ} (hN : 0 < N)
    (π : Measure (Spin N)) [IsProbabilityMeasure π]
    (eig : Fin N → ℝ) (U : Rotation N) (c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amp : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (v : ℕ → SpinTensorIndex I degree → ℝ≥0)
    (hb : CascadeExponents n b) (z : SpinTensorIndex I degree → ℝ) :
    let P := tensorLabeledLaw U I degree amp n b v
    let F := spinPriorLabeledLog π eig U c I degree amp n z
    let X := spinPriorCascadeValue π eig U c I degree amp n b v z
    Integrable F P ∧ (∫ p, F p ∂P) = X ∧
      Integrable (fun p => (F p-X)^2) P ∧
      (∫ p, (F p-X)^2 ∂P) ≤
        4 * ∫ T, (Real.log (rawTreeTotal n T).toReal)^2
          ∂(rawCascadeLaw n b : Measure (RawTree n)) := by
  sorry

end InvariantIsing

end

end OAI
end
