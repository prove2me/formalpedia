-- Prove2me | Theorems.Thm_OAI_Problem367_IsingCopyResponseRowPaths_copies_rows_summable_ae
-- name    : OAI.Problem367.IsingCopyResponseRowPaths.copies_rows_summable_ae
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T01:42:18.597495+00:00
-- url     : https://prove2.me/theorems/040cde52-0d8e-4c27-8bb0-6585b65d6ddd
-- title:
--   OAI.Problem367.IsingCopyResponseRowPaths.copies_rows_summable_ae: intermediate lemma from OpenAI, The sharp factor-of-IID threshold for the free Ising model on regular trees
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Problem367.free_ising_factor_iff_threshold`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The sharp factor-of-IID threshold for the free Ising model on regular trees*, OpenAI Math Release, September 26, 2026, result family 236, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Problem367.IsingCopyResponseRowPaths.copies_rows_summable_ae` of [lean/OAI/Probability/FreeIsing/Ising/CopyResponseRowSummability.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/FreeIsing/Ising/CopyResponseRowSummability.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Problem367.IsingCopyResponseRowPaths`, with `open MeasureTheory ProbabilityTheory`, `open scoped NNReal`, `open IsingObservationInnovation IsingObservationFactor IsingCopyStationarity`, `open PlantedSymmetry GaussianTreeCovariance`):
--
--   ```lean
--   theorem copies_rows_summable_ae
--       (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
--       {t : ℝ≥0} (ht : 0 < t)
--       (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1) :
--       ∀ᵐ q ∂copies beta μ,
--         Summable (fun v => row beta t v q.2.1 ^ 2) ∧
--           Summable (fun v => row beta t v q.2.2 ^ 2)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Problem367.IsingObservationFactor.copies`, `OAI.Problem367.IsingObservationInnovation.Paths`, `OAI.Problem367.WienerSampler.Path` and `OAI.Problem367.WienerSampler.pathMeasurableSpace` (definitions bundle `Q243FI000` of this split); `OAI.Problem367.IsingCopyResponseRowPaths.row` (definitions bundle `Q243FI004` of this split); `OAI.Problem367.HasFreeIsingLaw`, `OAI.Problem367.IsingSpin`, `OAI.Problem367.TreeVertex` and `OAI.Problem367.isingSpinMeasurable` (the published bundle `Def_FreeIsing`).
--
--   **Used by.** The proof of `OAI.Problem367.IsingCopyResponseRowPaths.integral_actual_density_le_path_sums` of this split imports it.
-- source:
--   OpenAI, The sharp factor-of-IID threshold for the free Ising model on regular trees, OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 236; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-sharp-factor-of-IID-threshold-for-the-free-Ising-model-on-regular-trees-September-26-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/FreeIsing/Ising/CopyResponseRowSummability.lean (declaration OAI.Problem367.IsingCopyResponseRowPaths.copies_rows_summable_ae)

import Mathlib
import Mathlib.MeasureTheory.Integral.Marginal
import Definitions.Def_FreeIsing
import Definitions.Def_Q243FI004

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367.IsingCopyResponseRowPaths
open IsingObservationInnovation IsingObservationFactor IsingCopyStationarity
open PlantedSymmetry GaussianTreeCovariance

variable {d : ℕ} {beta : ℝ}
variable {μ : Measure (TreeVertex d → IsingSpin)} [IsProbabilityMeasure μ]

theorem copies_rows_summable_ae
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    {t : ℝ≥0} (ht : 0 < t)
    (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1) :
    ∀ᵐ q ∂copies beta μ,
      Summable (fun v => row beta t v q.2.1 ^ 2) ∧
        Summable (fun v => row beta t v q.2.2 ^ 2) := by
  sorry

end Problem367.IsingCopyResponseRowPaths

end

end OAI
end
