-- Prove2me | Theorems.Thm_OAI_InvariantIsing_tensorDisorderPressure_conditional_mean
-- name    : OAI.InvariantIsing.tensorDisorderPressure_conditional_mean
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T05:57:58.372057+00:00
-- url     : https://prove2.me/theorems/4d09ae6a-b2c4-4d69-b1ef-833bc71ea22d
-- title:
--   OAI.InvariantIsing.tensorDisorderPressure_conditional_mean: intermediate lemma from OpenAI, All-temperature pressure for orthogonally invariant Ising spin glasses
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.InvariantIsing.gaussianPattern_ground_limit_unconditional`, `OAI.InvariantIsing.gaussianPattern_norm_limits_unconditional`, `OAI.InvariantIsing.gaussianPattern_pressure_limit_unconditional`, `OAI.InvariantIsing.ground_state_limit_unconditional`, `OAI.InvariantIsing.limiting_pressure_of_extreme_limits_unconditional`, `OAI.InvariantIsing.limiting_wasserstein_field_pressure_of_extreme_limits_unconditional`, `OAI.InvariantIsing.positive_temperature_pressure_unconditional`, `OAI.InvariantIsing.random_field_pressure_tendsto_ae_unconditional`, `OAI.InvariantIsing.random_pressure_limit_unconditional`, `OAI.InvariantIsing.random_pressure_tendsto_ae_unconditional` and `OAI.InvariantIsing.random_pressure_tendsto_in_measure_unconditional`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *All-temperature pressure for orthogonally invariant Ising spin glasses*, OpenAI Math Release, September 25, 2026, result family 234, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.InvariantIsing.tensorDisorderPressure_conditional_mean` of [lean/OAI/Probability/InvariantIsing/Arrays/NSpinTensorHaarFluctuation.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/InvariantIsing/Arrays/NSpinTensorHaarFluctuation.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.InvariantIsing`, with `open MeasureTheory ProbabilityTheory IsingPerceptron`, `open scoped BigOperators NNReal`):
--
--   ```lean
--   lemma tensorDisorderPressure_conditional_mean (hpub : GaussianLipschitzVarianceInput)
--       {N m k : ℕ} (hN : 0 < N) (eig c : Fin N → ℝ) (U : SpecialOrthogonal N)
--       (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
--       (n : ℕ) (b : ℕ → ℝ) (v : ℕ → SpinTensorIndex I degree → ℝ≥0)
--       (hb : CascadeExponents n b) (site : ℝ≥0) (monomial : Fin k → ℝ≥0) :
--       (∫ q, tensorDisorderPressure eig c I degree amplitude n (U, q)
--         ∂tensorRootTreeLaw I degree n b v (tensorVarianceProfile I degree site monomial)) =
--         tensorEnrichedPressure eig (specialRotation U) c I degree amplitude n b v
--           (tensorVarianceProfile I degree site monomial)
--   ```
--
--   **Definitions.** The statement is written with `OAI.InvariantIsing.SpinTensorIndex` (definitions bundle `OAIQ258000` of this split); `OAI.InvariantIsing.GaussianLipschitzVarianceInput`, `OAI.InvariantIsing.SpecialOrthogonal` and `OAI.InvariantIsing.specialRotation` (definitions bundle `OAIQ258001` of this split); `OAI.InvariantIsing.tensorVarianceProfile` (definitions bundle `OAIQ258003` of this split); `OAI.InvariantIsing.tensorRootTreeLaw` (definitions bundle `OAIQ258004` of this split); `OAI.InvariantIsing.tensorDisorderPressure` and `OAI.InvariantIsing.tensorEnrichedPressure` (definitions bundle `OAIQ258005` of this split); `OAI.IsingPerceptron.CascadeExponents`, `OAI.IsingPerceptron.NoiseTree` and `OAI.IsingPerceptron.noiseTreeMeasurableSpace` (definitions bundle `OAIQ4Ip000` of this split).
--
--   **Used by.** The proofs of `OAI.InvariantIsing.tensorDisorderPressure_variance` and `OAI.InvariantIsing.tensorPerturbationPressureMean_modulus` of this split import it.
-- source:
--   OpenAI, All-temperature pressure for orthogonally invariant Ising spin glasses, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 234; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/All-temperature-pressure-for-orthogonally-invariant-Ising-spin-glasses-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/InvariantIsing/Arrays/NSpinTensorHaarFluctuation.lean (declaration OAI.InvariantIsing.tensorDisorderPressure_conditional_mean)

import Mathlib
import Definitions.Def_OAIQ258005

section

attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityQuadraticResidualGibbs_probability _root_.OAI.InvariantIsing.cavityQuadraticResidualKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRootedPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualBaseKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualKernel_markov _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.InvariantIsing.vectorTerminalNoiseLaw_probability _root_.OAI.InvariantIsing.rootedResidualPrior_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators NNReal

namespace InvariantIsing

lemma tensorDisorderPressure_conditional_mean (hpub : GaussianLipschitzVarianceInput)
    {N m k : ℕ} (hN : 0 < N) (eig c : Fin N → ℝ) (U : SpecialOrthogonal N)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (v : ℕ → SpinTensorIndex I degree → ℝ≥0)
    (hb : CascadeExponents n b) (site : ℝ≥0) (monomial : Fin k → ℝ≥0) :
    (∫ q, tensorDisorderPressure eig c I degree amplitude n (U, q)
      ∂tensorRootTreeLaw I degree n b v (tensorVarianceProfile I degree site monomial)) =
      tensorEnrichedPressure eig (specialRotation U) c I degree amplitude n b v
        (tensorVarianceProfile I degree site monomial) := by
  sorry

end InvariantIsing

end

end OAI
end
