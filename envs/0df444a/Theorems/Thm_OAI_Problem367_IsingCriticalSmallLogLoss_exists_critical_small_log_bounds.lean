-- Prove2me | Theorems.Thm_OAI_Problem367_IsingCriticalSmallLogLoss_exists_critical_small_log_bounds
-- name    : OAI.Problem367.IsingCriticalSmallLogLoss.exists_critical_small_log_bounds
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T01:42:48.340842+00:00
-- url     : https://prove2.me/theorems/3b903bb1-97ed-4012-9e26-0223f577d02e
-- title:
--   OAI.Problem367.IsingCriticalSmallLogLoss.exists_critical_small_log_bounds: intermediate lemma from OpenAI, The sharp factor-of-IID threshold for the free Ising model on regular trees
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Problem367.free_ising_factor_iff_threshold`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The sharp factor-of-IID threshold for the free Ising model on regular trees*, OpenAI Math Release, September 26, 2026, result family 236, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Problem367.IsingCriticalSmallLogLoss.exists_critical_small_log_bounds` of [lean/OAI/Probability/FreeIsing/Ising/CriticalSmallLogLoss.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/FreeIsing/Ising/CriticalSmallLogLoss.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Problem367.IsingCriticalSmallLogLoss`, with `open MeasureTheory ProbabilityTheory`, `open scoped NNReal ENNReal`, `open IsingObservationInnovation IsingObservationFactor IsingCopySmallLogLoss`, `open IsingCopySpectral`):
--
--   ```lean
--   theorem exists_critical_small_log_bounds
--       (hd : 3 ≤ d) (hbeta : 0 ≤ beta)
--       (hcritical : ((d - 1 : ℕ) : ℝ) * (Real.tanh beta) ^ 2 = 1) :
--       ∃ c δ : ℝ, 0 < c ∧ 0 < δ ∧ δ < 1 ∧
--         ∀ (ν : Measure (TreeVertex d → IsingSpin)) [IsProbabilityMeasure ν],
--         HasFreeIsingLaw (Real.tanh beta) ν →
--         ∀ (T : ℝ≥0) (o v w : TreeVertex d), treeAdj v w →
--         ∀ (t : ℝ≥0), 0 < (t : ℝ) → t ≤ T → (t : ℝ) ≤ δ →
--         (logVariance hbeta ν v w t ≤
--           cavityLogVarianceCoefficient (Real.tanh beta) * (t : ℝ) ^ (1 / 4 : ℝ) *
--             siteVariance beta ν o t +
--           min (cavityLogVarianceCoefficient (Real.tanh beta) * siteVariance beta ν o t)
--             (cavityLogTailCoefficient (Real.tanh beta)
--               (2 * (T : ℝ) + 2 * (d : ℝ) * beta) *
--                 Real.exp (-c * (Real.log (1 / (t : ℝ))) ^ 2))) ∧
--         (0 < siteVariance beta ν o t →
--           logVariance hbeta ν v w t ≤
--             (cavityLogVarianceCoefficient (Real.tanh beta) +
--               2 * (cavityLogVarianceCoefficient (Real.tanh beta) +
--                 cavityLogTailCoefficient (Real.tanh beta)
--                   (2 * (T : ℝ) + 2 * (d : ℝ) * beta)) / c) *
--               siteVariance beta ν o t *
--               ((t : ℝ) ^ (1 / 4 : ℝ) +
--                 (1 + Real.log (varianceScale d beta T / siteVariance beta ν o t)) /
--                   (Real.log (1 / (t : ℝ))) ^ 2))
--   ```
--
--   **Definitions.** The statement is written with `OAI.Problem367.IsingCopySmallLogLoss.siteVariance` (definitions bundle `Q243FI000` of this split); `OAI.Problem367.cavityLogTailCoefficient`, `OAI.Problem367.cavityLogVarianceCoefficient` and `OAI.Problem367.IsingCriticalSmallLogLoss.varianceScale` (definitions bundle `Q243FI001` of this split); `OAI.Problem367.IsingCopySmallLogLoss.logVariance` (definitions bundle `Q243FI004` of this split); `OAI.Problem367.HasFreeIsingLaw`, `OAI.Problem367.IsingSpin`, `OAI.Problem367.TreeVertex`, `OAI.Problem367.isingSpinMeasurable` and `OAI.Problem367.treeAdj` (the published bundle `Def_FreeIsing`).
--
--   **Used by.** The proof of `OAI.Problem367.IsingCopyResponseRowPaths.critical_root_variance_zero_of_noise_bound` of this split imports it.
-- source:
--   OpenAI, The sharp factor-of-IID threshold for the free Ising model on regular trees, OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 236; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-sharp-factor-of-IID-threshold-for-the-free-Ising-model-on-regular-trees-September-26-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/FreeIsing/Ising/CriticalSmallLogLoss.lean (declaration OAI.Problem367.IsingCriticalSmallLogLoss.exists_critical_small_log_bounds)

import Mathlib
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
open scoped NNReal ENNReal

namespace Problem367.IsingCriticalSmallLogLoss

open IsingObservationInnovation IsingObservationFactor IsingCopySmallLogLoss
open IsingCopySpectral

variable {d : ℕ} {beta : ℝ}
variable {μ : Measure (TreeVertex d → IsingSpin)} [IsProbabilityMeasure μ]

theorem exists_critical_small_log_bounds
    (hd : 3 ≤ d) (hbeta : 0 ≤ beta)
    (hcritical : ((d - 1 : ℕ) : ℝ) * (Real.tanh beta) ^ 2 = 1) :
    ∃ c δ : ℝ, 0 < c ∧ 0 < δ ∧ δ < 1 ∧
      ∀ (ν : Measure (TreeVertex d → IsingSpin)) [IsProbabilityMeasure ν],
      HasFreeIsingLaw (Real.tanh beta) ν →
      ∀ (T : ℝ≥0) (o v w : TreeVertex d), treeAdj v w →
      ∀ (t : ℝ≥0), 0 < (t : ℝ) → t ≤ T → (t : ℝ) ≤ δ →
      (logVariance hbeta ν v w t ≤
        cavityLogVarianceCoefficient (Real.tanh beta) * (t : ℝ) ^ (1 / 4 : ℝ) *
          siteVariance beta ν o t +
        min (cavityLogVarianceCoefficient (Real.tanh beta) * siteVariance beta ν o t)
          (cavityLogTailCoefficient (Real.tanh beta)
            (2 * (T : ℝ) + 2 * (d : ℝ) * beta) *
              Real.exp (-c * (Real.log (1 / (t : ℝ))) ^ 2))) ∧
      (0 < siteVariance beta ν o t →
        logVariance hbeta ν v w t ≤
          (cavityLogVarianceCoefficient (Real.tanh beta) +
            2 * (cavityLogVarianceCoefficient (Real.tanh beta) +
              cavityLogTailCoefficient (Real.tanh beta)
                (2 * (T : ℝ) + 2 * (d : ℝ) * beta)) / c) *
            siteVariance beta ν o t *
            ((t : ℝ) ^ (1 / 4 : ℝ) +
              (1 + Real.log (varianceScale d beta T / siteVariance beta ν o t)) /
                (Real.log (1 / (t : ℝ))) ^ 2)) := by
  sorry

end Problem367.IsingCriticalSmallLogLoss

end

end OAI
end
