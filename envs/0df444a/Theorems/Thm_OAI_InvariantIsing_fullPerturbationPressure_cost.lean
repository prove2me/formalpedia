-- Prove2me | Theorems.Thm_OAI_InvariantIsing_fullPerturbationPressure_cost
-- name    : OAI.InvariantIsing.fullPerturbationPressure_cost
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T05:38:32.131207+00:00
-- url     : https://prove2.me/theorems/04478987-8e58-4b41-ad80-37e156abdef9
-- title:
--   OAI.InvariantIsing.fullPerturbationPressure_cost: intermediate lemma from OpenAI, All-temperature pressure for orthogonally invariant Ising spin glasses
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.InvariantIsing.gaussianPattern_ground_limit_unconditional`, `OAI.InvariantIsing.gaussianPattern_norm_limits_unconditional`, `OAI.InvariantIsing.gaussianPattern_pressure_limit_unconditional`, `OAI.InvariantIsing.ground_state_limit_unconditional`, `OAI.InvariantIsing.limiting_pressure_of_extreme_limits_unconditional`, `OAI.InvariantIsing.limiting_wasserstein_field_pressure_of_extreme_limits_unconditional`, `OAI.InvariantIsing.positive_temperature_pressure_unconditional`, `OAI.InvariantIsing.random_field_pressure_tendsto_ae_unconditional`, `OAI.InvariantIsing.random_pressure_limit_unconditional`, `OAI.InvariantIsing.random_pressure_tendsto_ae_unconditional` and `OAI.InvariantIsing.random_pressure_tendsto_in_measure_unconditional`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *All-temperature pressure for orthogonally invariant Ising spin glasses*, OpenAI Math Release, September 25, 2026, result family 234, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.InvariantIsing.fullPerturbationPressure_cost` of [lean/OAI/Probability/InvariantIsing/Arrays/FullPerturbationCost.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/InvariantIsing/Arrays/FullPerturbationCost.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.InvariantIsing`, with `open MeasureTheory ProbabilityTheory IsingPerceptron`, `open scoped BigOperators NNReal`):
--
--   ```lean
--   theorem fullPerturbationPressure_cost {N m : ℕ} (hN : 0 < N)
--       (eig c : Fin N → ℝ) (U : Rotation N) (I : Fin m → Finset (Fin N))
--       (degree : Fin N → Fin m → ℕ) (u : Fin N → ℝ) (hu : ∀ j, |u j| ≤ 2)
--       (z : Fin m → ℝ) (hz : ∀ a, |z a| ≤ 2) (t : ℝ)
--       (n : ℕ) (r : Fin N → ℕ) (b : ℕ → ℝ) (hb : CascadeExponents n b)
--       (h : ℕ → ℝ) (hh : Monotone h) (h0 : 0 ≤ h 0) :
--       let v := tensorPathProfile I degree n r h
--       |tensorEnrichedPressure (diagonalPerturbedEigenvalues eig I z t) U c I degree
--           (tensorPerturbationAmplitude N u) n b (fun i => v (i + 1)) (v 0) -
--         tensorEnrichedPressure (fun i => t * eig i) U c I degree 0 n b
--           (fun i => v (i + 1)) (v 0)| ≤
--         2 * m * perturbationScale N + 8 * perturbationScale N ^ 2
--   ```
--
--   **Definitions.** The statement is written with `OAI.InvariantIsing.SpinTensorIndex` (definitions bundle `OAIQ258000` of this split); `OAI.InvariantIsing.diagonalPerturbedEigenvalues` and `OAI.InvariantIsing.tensorPerturbationAmplitude` (definitions bundle `OAIQ258001` of this split); `OAI.InvariantIsing.tensorPathProfile` (definitions bundle `OAIQ258003` of this split); `OAI.InvariantIsing.tensorEnrichedPressure` (definitions bundle `OAIQ258005` of this split); `OAI.IsingPerceptron.CascadeExponents` and `OAI.IsingPerceptron.perturbationScale` (definitions bundle `OAIQ4Ip000` of this split); `OAI.InvariantIsing.Rotation` (the published bundle `Def_InvariantIsing`).
--
--   **Used by.** The proof of `OAI.InvariantIsing.tensorNamespacedMeanPressure_perturbation_cost` of this split imports it.
-- source:
--   OpenAI, All-temperature pressure for orthogonally invariant Ising spin glasses, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 234; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/All-temperature-pressure-for-orthogonally-invariant-Ising-spin-glasses-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/InvariantIsing/Arrays/FullPerturbationCost.lean (declaration OAI.InvariantIsing.fullPerturbationPressure_cost)

import Mathlib
import Definitions.Def_InvariantIsing
import Definitions.Def_OAIQ258005

section

attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorRootTreeLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators NNReal

namespace InvariantIsing

theorem fullPerturbationPressure_cost {N m : ℕ} (hN : 0 < N)
    (eig c : Fin N → ℝ) (U : Rotation N) (I : Fin m → Finset (Fin N))
    (degree : Fin N → Fin m → ℕ) (u : Fin N → ℝ) (hu : ∀ j, |u j| ≤ 2)
    (z : Fin m → ℝ) (hz : ∀ a, |z a| ≤ 2) (t : ℝ)
    (n : ℕ) (r : Fin N → ℕ) (b : ℕ → ℝ) (hb : CascadeExponents n b)
    (h : ℕ → ℝ) (hh : Monotone h) (h0 : 0 ≤ h 0) :
    let v := tensorPathProfile I degree n r h
    |tensorEnrichedPressure (diagonalPerturbedEigenvalues eig I z t) U c I degree
        (tensorPerturbationAmplitude N u) n b (fun i => v (i + 1)) (v 0) -
      tensorEnrichedPressure (fun i => t * eig i) U c I degree 0 n b
        (fun i => v (i + 1)) (v 0)| ≤
      2 * m * perturbationScale N + 8 * perturbationScale N ^ 2 := by
  sorry

end InvariantIsing

end

end OAI
end
