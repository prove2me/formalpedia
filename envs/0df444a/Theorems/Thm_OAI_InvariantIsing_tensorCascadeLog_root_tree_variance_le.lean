-- Prove2me | Theorems.Thm_OAI_InvariantIsing_tensorCascadeLog_root_tree_variance_le
-- name    : OAI.InvariantIsing.tensorCascadeLog_root_tree_variance_le
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T05:58:13.327469+00:00
-- url     : https://prove2.me/theorems/3b79b3f3-0298-43bc-90e1-0d2846c5347a
-- title:
--   OAI.InvariantIsing.tensorCascadeLog_root_tree_variance_le: intermediate lemma from OpenAI, All-temperature pressure for orthogonally invariant Ising spin glasses
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.InvariantIsing.gaussianPattern_ground_limit_unconditional`, `OAI.InvariantIsing.gaussianPattern_norm_limits_unconditional`, `OAI.InvariantIsing.gaussianPattern_pressure_limit_unconditional`, `OAI.InvariantIsing.ground_state_limit_unconditional`, `OAI.InvariantIsing.limiting_pressure_of_extreme_limits_unconditional`, `OAI.InvariantIsing.limiting_wasserstein_field_pressure_of_extreme_limits_unconditional`, `OAI.InvariantIsing.positive_temperature_pressure_unconditional`, `OAI.InvariantIsing.random_field_pressure_tendsto_ae_unconditional`, `OAI.InvariantIsing.random_pressure_limit_unconditional`, `OAI.InvariantIsing.random_pressure_tendsto_ae_unconditional` and `OAI.InvariantIsing.random_pressure_tendsto_in_measure_unconditional`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *All-temperature pressure for orthogonally invariant Ising spin glasses*, OpenAI Math Release, September 25, 2026, result family 234, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.InvariantIsing.tensorCascadeLog_root_tree_variance_le` of [lean/OAI/Probability/InvariantIsing/Arrays/NSpinTensorFluctuation.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/InvariantIsing/Arrays/NSpinTensorFluctuation.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.InvariantIsing`, with `open MeasureTheory ProbabilityTheory`, `open scoped BigOperators NNReal`):
--
--   ```lean
--   theorem tensorCascadeLog_root_tree_variance_le (hpub : GaussianLipschitzVarianceInput)
--       {N m k : ℕ} (hN : 0 < N) (eig : Fin N → ℝ) (U : Rotation N) (c : Fin N → ℝ)
--       (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
--       (n : ℕ) (b : ℕ → ℝ) (v : ℕ → SpinTensorIndex I degree → ℝ≥0)
--       (hb : IsingPerceptron.CascadeExponents n b) (site : ℝ≥0) (monomial : Fin k → ℝ≥0) :
--       let root := tensorGaussianLaw I degree (tensorVarianceProfile I degree site monomial)
--       let P := (root : Measure (SpinTensorIndex I degree → ℝ)).prod (tensorCascadeLaw I degree n b v)
--       let F := fun p : (SpinTensorIndex I degree → ℝ) ×
--         IsingPerceptron.NoiseTree (SpinTensorIndex I degree → ℝ) n =>
--         tensorCascadeLog eig U c I degree amplitude n p.1 p.2
--       MemLp F 2 P ∧ variance F P ≤
--         4 * (∫ T, (Real.log (IsingPerceptron.rawTreeTotal n T).toReal) ^ 2
--           ∂(IsingPerceptron.rawCascadeLaw n b : Measure (IsingPerceptron.RawTree n))) +
--         (site : ℝ) * N + ∑ j, (monomial j : ℝ) * amplitude j ^ 2
--   ```
--
--   **Definitions.** The statement is written with `OAI.InvariantIsing.SpinTensorIndex` (definitions bundle `OAIQ258000` of this split); `OAI.InvariantIsing.GaussianLipschitzVarianceInput` (definitions bundle `OAIQ258001` of this split); `OAI.InvariantIsing.tensorVarianceProfile` (definitions bundle `OAIQ258003` of this split); `OAI.InvariantIsing.tensorCascadeLaw` and `OAI.InvariantIsing.tensorGaussianLaw` (definitions bundle `OAIQ258004` of this split); `OAI.InvariantIsing.tensorCascadeLog` (definitions bundle `OAIQ258005` of this split); `OAI.IsingPerceptron.CascadeExponents`, `OAI.IsingPerceptron.NoiseTree`, `OAI.IsingPerceptron.RawTree`, `OAI.IsingPerceptron.noiseTreeMeasurableSpace`, `OAI.IsingPerceptron.rawCascadeLaw`, `OAI.IsingPerceptron.rawTreeMeasurableSpace` and `OAI.IsingPerceptron.rawTreeTotal` (definitions bundle `OAIQ4Ip000` of this split); `OAI.InvariantIsing.Rotation` (the published bundle `Def_InvariantIsing`).
--
--   **Used by.** The proofs of `OAI.InvariantIsing.tensorDisorderPressure_conditional_mean` and `OAI.InvariantIsing.tensorDisorderPressure_variance` of this split import it.
-- source:
--   OpenAI, All-temperature pressure for orthogonally invariant Ising spin glasses, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 234; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/All-temperature-pressure-for-orthogonally-invariant-Ising-spin-glasses-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/InvariantIsing/Arrays/NSpinTensorFluctuation.lean (declaration OAI.InvariantIsing.tensorCascadeLog_root_tree_variance_le)

import Mathlib
import Definitions.Def_InvariantIsing
import Definitions.Def_OAIQ258005

section

attribute [-instance] _root_.OAI.InvariantIsing.cavityQuadraticResidualGibbs_probability _root_.OAI.InvariantIsing.cavityQuadraticResidualKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRootedPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualBaseKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualKernel_markov _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty _root_.OAI.InvariantIsing.tensorCoordinateLaw_probability _root_.OAI.InvariantIsing.tensorLabeledLaw_probability _root_.OAI.InvariantIsing.tensorRootTreeLaw_probability _root_.OAI.InvariantIsing.vectorTerminalNoiseLaw_probability _root_.OAI.InvariantIsing.rootedResidualPrior_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

namespace InvariantIsing

theorem tensorCascadeLog_root_tree_variance_le (hpub : GaussianLipschitzVarianceInput)
    {N m k : ℕ} (hN : 0 < N) (eig : Fin N → ℝ) (U : Rotation N) (c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (v : ℕ → SpinTensorIndex I degree → ℝ≥0)
    (hb : IsingPerceptron.CascadeExponents n b) (site : ℝ≥0) (monomial : Fin k → ℝ≥0) :
    let root := tensorGaussianLaw I degree (tensorVarianceProfile I degree site monomial)
    let P := (root : Measure (SpinTensorIndex I degree → ℝ)).prod (tensorCascadeLaw I degree n b v)
    let F := fun p : (SpinTensorIndex I degree → ℝ) ×
      IsingPerceptron.NoiseTree (SpinTensorIndex I degree → ℝ) n =>
      tensorCascadeLog eig U c I degree amplitude n p.1 p.2
    MemLp F 2 P ∧ variance F P ≤
      4 * (∫ T, (Real.log (IsingPerceptron.rawTreeTotal n T).toReal) ^ 2
        ∂(IsingPerceptron.rawCascadeLaw n b : Measure (IsingPerceptron.RawTree n))) +
      (site : ℝ) * N + ∑ j, (monomial j : ℝ) * amplitude j ^ 2 := by
  sorry

end InvariantIsing

end

end OAI
end
