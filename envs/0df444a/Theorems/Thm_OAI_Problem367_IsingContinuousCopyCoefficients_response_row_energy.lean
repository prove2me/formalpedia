-- Prove2me | Theorems.Thm_OAI_Problem367_IsingContinuousCopyCoefficients_response_row_energy
-- name    : OAI.Problem367.IsingContinuousCopyCoefficients.response_row_energy
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T01:44:45.543608+00:00
-- url     : https://prove2.me/theorems/43d923c2-fdda-41b5-9a69-bcbe8a6efa08
-- title:
--   OAI.Problem367.IsingContinuousCopyCoefficients.response_row_energy: intermediate lemma from OpenAI, The sharp factor-of-IID threshold for the free Ising model on regular trees
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Problem367.free_ising_factor_iff_threshold`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The sharp factor-of-IID threshold for the free Ising model on regular trees*, OpenAI Math Release, September 26, 2026, result family 236, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Problem367.IsingContinuousCopyCoefficients.response_row_energy` of [lean/OAI/Probability/FreeIsing/Ising/ContinuousCopyCoefficients.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/FreeIsing/Ising/ContinuousCopyCoefficients.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Problem367.IsingContinuousCopyCoefficients`, with `open MeasureTheory ProbabilityTheory Filter Set`, `open scoped NNReal Topology`, `open IsingObservationInnovation IsingObservationFactor IsingCopyEnergy`):
--
--   ```lean
--   theorem response_row_energy (hd : 3 ≤ d)
--       (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
--       (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1)
--       (j : Bool) (T : ℝ≥0) :
--       (∀ᵐ p ∂((volume.restrict (Ioc (0 : ℝ) (T : ℝ))).prod (copies beta μ)),
--         Summable (fun v => response hb j v p.1.toNNReal p.2 ^ 2)) ∧
--       Integrable (fun p : ℝ × Joint d => ∑' v, response hb j v p.1.toNNReal p.2 ^ 2)
--         ((volume.restrict (Ioc (0 : ℝ) (T : ℝ))).prod (copies beta μ))
--   ```
--
--   **Definitions.** The statement is written with `OAI.Problem367.IsingCopyEnergy.Joint`, `OAI.Problem367.IsingObservationFactor.copies`, `OAI.Problem367.IsingObservationInnovation.Paths`, `OAI.Problem367.WienerSampler.Path` and `OAI.Problem367.WienerSampler.pathMeasurableSpace` (definitions bundle `Q243FI000` of this split); `OAI.Problem367.IsingContinuousCopyCoefficients.response` (definitions bundle `Q243FI005` of this split); `OAI.Problem367.HasFreeIsingLaw`, `OAI.Problem367.IsingSpin`, `OAI.Problem367.TreeVertex` and `OAI.Problem367.isingSpinMeasurable` (the published bundle `Def_FreeIsing`).
--
--   **Used by.** The proofs of `OAI.Problem367.IsingJoinedResponseIntegrals.exists_integrals` and `OAI.Problem367.IsingObservationFactor.variance_analysis_of_joined_decomposition` of this split import it.
-- source:
--   OpenAI, The sharp factor-of-IID threshold for the free Ising model on regular trees, OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 236; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-sharp-factor-of-IID-threshold-for-the-free-Ising-model-on-regular-trees-September-26-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/FreeIsing/Ising/ContinuousCopyCoefficients.lean (declaration OAI.Problem367.IsingContinuousCopyCoefficients.response_row_energy)

import Mathlib
import Mathlib.MeasureTheory.Integral.Marginal
import Definitions.Def_FreeIsing
import Definitions.Def_Q243FI005

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal Topology

namespace Problem367.IsingContinuousCopyCoefficients
open IsingObservationInnovation IsingObservationFactor IsingCopyEnergy

variable {d : ℕ} {beta : ℝ}

variable {μ : Measure (TreeVertex d → IsingSpin)} [IsProbabilityMeasure μ]

theorem response_row_energy (hd : 3 ≤ d)
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1)
    (j : Bool) (T : ℝ≥0) :
    (∀ᵐ p ∂((volume.restrict (Ioc (0 : ℝ) (T : ℝ))).prod (copies beta μ)),
      Summable (fun v => response hb j v p.1.toNNReal p.2 ^ 2)) ∧
    Integrable (fun p : ℝ × Joint d => ∑' v, response hb j v p.1.toNNReal p.2 ^ 2)
      ((volume.restrict (Ioc (0 : ℝ) (T : ℝ))).prod (copies beta μ)) := by
  sorry

end Problem367.IsingContinuousCopyCoefficients

end

end OAI
end
