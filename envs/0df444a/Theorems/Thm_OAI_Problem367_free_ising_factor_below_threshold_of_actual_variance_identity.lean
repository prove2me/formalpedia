-- Prove2me | Theorems.Thm_OAI_Problem367_free_ising_factor_below_threshold_of_actual_variance_identity
-- name    : OAI.Problem367.free_ising_factor_below_threshold_of_actual_variance_identity
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T01:44:09.990649+00:00
-- url     : https://prove2.me/theorems/c4493bdd-45da-407b-8875-a67a74da59fa
-- title:
--   OAI.Problem367.free_ising_factor_below_threshold_of_actual_variance_identity: intermediate lemma from OpenAI, The sharp factor-of-IID threshold for the free Ising model on regular trees
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Problem367.free_ising_factor_iff_threshold`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The sharp factor-of-IID threshold for the free Ising model on regular trees*, OpenAI Math Release, September 26, 2026, result family 236, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Problem367.free_ising_factor_below_threshold_of_actual_variance_identity` of [lean/OAI/Probability/FreeIsing/Ising/SharpVarianceRecovery.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/FreeIsing/Ising/SharpVarianceRecovery.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Problem367`, with `open MeasureTheory ProbabilityTheory Set`, `open scoped NNReal`, `open IsingObservationInnovation IsingObservationFactor IsingCopySmallLogLoss`, `open ConnectedHull`):
--
--   ```lean
--   theorem free_ising_factor_below_threshold_of_actual_variance_identity
--       (hvariance : ∀ (d : ℕ) (beta : ℝ), 3 ≤ d → 0 < beta →
--         ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1 →
--         ActualRootVarianceIdentity beta (freeIsingMeasure d (Real.tanh beta))) :
--       ∀ (d : ℕ) (beta : ℝ), 3 ≤ d → 0 ≤ beta →
--         Real.tanh beta ≤ 1 / Real.sqrt ((d : ℝ) - 1) →
--         IsFactorOfIID d (Real.tanh beta)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Problem367.ActualRootVarianceIdentity` (definitions bundle `Q243FI000` of this split); `OAI.Problem367.freeIsingMeasure` and `OAI.Problem367.freeIsingMeasure_probability` (definitions bundle `Q243FI004` of this split); `OAI.Problem367.IsFactorOfIID` (the published bundle `Def_FreeIsing`).
--
--   **Used by.** The proof of `OAI.Problem367.free_ising_factor_iff_threshold` of this split imports it.
-- source:
--   OpenAI, The sharp factor-of-IID threshold for the free Ising model on regular trees, OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 236; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-sharp-factor-of-IID-threshold-for-the-free-Ising-model-on-regular-trees-September-26-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/FreeIsing/Ising/SharpVarianceRecovery.lean (declaration OAI.Problem367.free_ising_factor_below_threshold_of_actual_variance_identity)

import Mathlib
import Mathlib.MeasureTheory.Function.FactorsThrough
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
open MeasureTheory ProbabilityTheory Set
open scoped NNReal

namespace Problem367
open IsingObservationInnovation IsingObservationFactor IsingCopySmallLogLoss
open ConnectedHull

theorem free_ising_factor_below_threshold_of_actual_variance_identity
    (hvariance : ∀ (d : ℕ) (beta : ℝ), 3 ≤ d → 0 < beta →
      ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1 →
      ActualRootVarianceIdentity beta (freeIsingMeasure d (Real.tanh beta))) :
    ∀ (d : ℕ) (beta : ℝ), 3 ≤ d → 0 ≤ beta →
      Real.tanh beta ≤ 1 / Real.sqrt ((d : ℝ) - 1) →
      IsFactorOfIID d (Real.tanh beta) := by
  sorry

end Problem367

end

end OAI
end
