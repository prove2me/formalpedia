-- Prove2me | Theorems.Thm_OAI_Problem367_IsingJoinedResponseIntegrals_exists_integrals
-- name    : OAI.Problem367.IsingJoinedResponseIntegrals.exists_integrals
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T01:46:55.197137+00:00
-- url     : https://prove2.me/theorems/e02d6596-af6e-4722-9d85-85f31e0ff7a1
-- title:
--   OAI.Problem367.IsingJoinedResponseIntegrals.exists_integrals: intermediate lemma from OpenAI, The sharp factor-of-IID threshold for the free Ising model on regular trees
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Problem367.free_ising_factor_iff_threshold`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The sharp factor-of-IID threshold for the free Ising model on regular trees*, OpenAI Math Release, September 26, 2026, result family 236, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Problem367.IsingJoinedResponseIntegrals.exists_integrals` of [lean/OAI/Probability/FreeIsing/Ising/JoinedResponseIntegrals.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/FreeIsing/Ising/JoinedResponseIntegrals.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Problem367.IsingJoinedResponseIntegrals`, with `open MeasureTheory ProbabilityTheory Filter`, `open scoped NNReal Topology`, `open IsingObservationInnovation IsingObservationFactor IsingCopyEnergy`, `open IsingContinuousCopyCoefficients BrownianArrayFiltration`):
--
--   ```lean
--   theorem exists_integrals
--       {μ : Measure (TreeVertex d → IsingSpin)} [IsProbabilityMeasure μ]
--       (hd : 3 ≤ d) (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
--       (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1) :
--       Nonempty (IntegralSystem hb μ)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Problem367.IsingJoinedResponseIntegrals.IntegralSystem` (definitions bundle `Q243FI005` of this split); `OAI.Problem367.HasFreeIsingLaw`, `OAI.Problem367.IsingSpin`, `OAI.Problem367.TreeVertex` and `OAI.Problem367.isingSpinMeasurable` (the published bundle `Def_FreeIsing`).
--
--   **Used by.** The proof of `OAI.Problem367.IsingObservationFactor.actual_variance_analysis` of this split imports it.
-- source:
--   OpenAI, The sharp factor-of-IID threshold for the free Ising model on regular trees, OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 236; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-sharp-factor-of-IID-threshold-for-the-free-Ising-model-on-regular-trees-September-26-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/FreeIsing/Ising/JoinedResponseIntegrals.lean (declaration OAI.Problem367.IsingJoinedResponseIntegrals.exists_integrals)

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
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

namespace Problem367.IsingJoinedResponseIntegrals
open IsingObservationInnovation IsingObservationFactor IsingCopyEnergy
open IsingContinuousCopyCoefficients BrownianArrayFiltration

variable {d : ℕ} {beta : ℝ}

theorem exists_integrals
    {μ : Measure (TreeVertex d → IsingSpin)} [IsProbabilityMeasure μ]
    (hd : 3 ≤ d) (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1) :
    Nonempty (IntegralSystem hb μ) := by
  sorry

end Problem367.IsingJoinedResponseIntegrals

end

end OAI
end
