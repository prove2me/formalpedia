-- Prove2me | Theorems.Thm_OAI_Problem367_IsingCopySpectral_forwardOperator_pow_bound
-- name    : OAI.Problem367.IsingCopySpectral.forwardOperator_pow_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T01:46:48.283197+00:00
-- url     : https://prove2.me/theorems/6a6d0d56-18a7-49cf-81e5-7be95f56b202
-- title:
--   OAI.Problem367.IsingCopySpectral.forwardOperator_pow_bound: intermediate lemma from OpenAI, The sharp factor-of-IID threshold for the free Ising model on regular trees
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Problem367.free_ising_factor_iff_threshold`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The sharp factor-of-IID threshold for the free Ising model on regular trees*, OpenAI Math Release, September 26, 2026, result family 236, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Problem367.IsingCopySpectral.forwardOperator_pow_bound` of [lean/OAI/Probability/FreeIsing/Ising/CopySpectral.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/FreeIsing/Ising/CopySpectral.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Problem367.IsingCopySpectral`, with `open MeasureTheory ProbabilityTheory`, `open scoped NNReal`, `open IsingObservationInnovation IsingObservationFactor IsingCopyStationarity`):
--
--   ```lean
--   theorem forwardOperator_pow_bound
--       (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hd : 3 ≤ d) (hbeta : 0 ≤ beta)
--       (hthreshold : Real.tanh beta ≤ 1 / Real.sqrt ((d : ℝ) - 1)) :
--       ∃ K : ℝ, 0 ≤ K ∧ ∀ n : ℕ,
--         ‖ColoredEdgeLifts.forwardOperator (by omega : 0 < d)
--           (differenceReflection hμ) ((d : ℝ) - 1)⁻¹ ^ n‖ ≤
--           K * ((n : ℝ) + 1) * (Real.sqrt ((d : ℝ) - 1))⁻¹ ^ n
--   ```
--
--   **Definitions.** The statement is written with `OAI.Problem367.IsingObservationFactor.copies`, `OAI.Problem367.IsingObservationInnovation.Paths`, `OAI.Problem367.IsingObservationInnovation.observationLaw`, `OAI.Problem367.WienerSampler.Path` and `OAI.Problem367.WienerSampler.pathMeasurableSpace` (definitions bundle `Q243FI000` of this split); `OAI.Problem367.ColoredEdgeLifts.EdgeSpace`, `OAI.Problem367.ColoredEdgeLifts.forwardOperator`, `OAI.Problem367.CopyDifference.operator` and `OAI.Problem367.CopyDifference.rangeClosure_completeSpace` (definitions bundle `Q243FI001` of this split); `OAI.Problem367.IsingCopySpectral.differenceReflection`, `OAI.Problem367.IsingCopySpectral.differenceSpace` and `OAI.Problem367.IsingCopyStationarity.measurePreserving_observations` (definitions bundle `Q243FI005` of this split); `OAI.Problem367.HasFreeIsingLaw`, `OAI.Problem367.IsingSpin`, `OAI.Problem367.TreeVertex` and `OAI.Problem367.isingSpinMeasurable` (the published bundle `Def_FreeIsing`).
--
--   **Used by.** The proofs of `OAI.Problem367.IsingCopyResponseRowPaths.exists_actual_spatial_endpoint_constant` and `OAI.Problem367.IsingCopyResponseRowPaths.exists_noise_energy_long_constants` of this split import it.
-- source:
--   OpenAI, The sharp factor-of-IID threshold for the free Ising model on regular trees, OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 236; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-sharp-factor-of-IID-threshold-for-the-free-Ising-model-on-regular-trees-September-26-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/FreeIsing/Ising/CopySpectral.lean (declaration OAI.Problem367.IsingCopySpectral.forwardOperator_pow_bound)

import Mathlib
import Definitions.Def_FreeIsing
import Definitions.Def_Q243FI005

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367.IsingCopySpectral

open IsingObservationInnovation IsingObservationFactor IsingCopyStationarity

variable {d : ℕ} {beta : ℝ}
variable {μ : Measure (TreeVertex d → IsingSpin)} [IsProbabilityMeasure μ]

theorem forwardOperator_pow_bound
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hd : 3 ≤ d) (hbeta : 0 ≤ beta)
    (hthreshold : Real.tanh beta ≤ 1 / Real.sqrt ((d : ℝ) - 1)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ n : ℕ,
      ‖ColoredEdgeLifts.forwardOperator (by omega : 0 < d)
        (differenceReflection hμ) ((d : ℝ) - 1)⁻¹ ^ n‖ ≤
        K * ((n : ℝ) + 1) * (Real.sqrt ((d : ℝ) - 1))⁻¹ ^ n := by
  sorry

end Problem367.IsingCopySpectral

end

end OAI
end
