-- Prove2me | Theorems.Thm_OAI_Problem367_IsingObservationFactor_siteVariance_eq_zero_of_subcritical_actual_variance_identity
-- name    : OAI.Problem367.IsingObservationFactor.siteVariance_eq_zero_of_subcritical_actual_variance_identity
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T01:39:08.517188+00:00
-- url     : https://prove2.me/theorems/c707575f-c102-4bab-b570-00f57979e667
-- title:
--   OAI.Problem367.IsingObservationFactor.siteVariance_eq_zero_of_subcritical_actual_variance_identity (OpenAI intermediate lemma)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Problem367.free_ising_factor_iff_threshold`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The sharp factor-of-IID threshold for the free Ising model on regular trees*, OpenAI Math Release, September 26, 2026, result family 236, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Problem367.IsingObservationFactor.siteVariance_eq_zero_of_subcritical_actual_variance_identity` of [lean/OAI/Probability/FreeIsing/Ising/StrictFactorRecovery.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/FreeIsing/Ising/StrictFactorRecovery.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Problem367.IsingObservationFactor`, with `open MeasureTheory ProbabilityTheory Set`, `open scoped NNReal`, `open IsingObservationInnovation IsingCopySmallLogLoss`, `open ConnectedHull`):
--
--   ```lean
--   theorem siteVariance_eq_zero_of_subcritical_actual_variance_identity
--       (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
--       (hstrict : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 < 1) (T : ℝ≥0)
--       (hAC : AbsolutelyContinuousOnInterval
--         (fun t : ℝ => siteVariance beta μ (root d) t.toNNReal) 0 (T : ℝ))
--       (hderiv : ∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) (T : ℝ)),
--         deriv (fun s : ℝ => siteVariance beta μ (root d) s.toNNReal) t =
--           ∫ q, IsingCopyEnergy.density beta (root d) t q ∂copies beta μ) :
--       ∀ t : ℝ≥0, t ≤ T → siteVariance beta μ (root d) t = 0
--   ```
--
--   **Definitions.** The statement is written with `OAI.Problem367.ConnectedHull.root`, `OAI.Problem367.IsingCopyEnergy.density`, `OAI.Problem367.IsingCopySmallLogLoss.siteVariance`, `OAI.Problem367.IsingObservationFactor.copies`, `OAI.Problem367.IsingObservationInnovation.Paths`, `OAI.Problem367.WienerSampler.Path` and `OAI.Problem367.WienerSampler.pathMeasurableSpace` (definitions bundle `Q243FI000` of this split); `OAI.Problem367.HasFreeIsingLaw`, `OAI.Problem367.IsingSpin`, `OAI.Problem367.TreeVertex` and `OAI.Problem367.isingSpinMeasurable` (the published bundle `Def_FreeIsing`).
--
--   **Used by.** The proof of `OAI.Problem367.free_ising_factor_below_threshold_of_actual_variance_identity` of this split imports it.
-- source:
--   OpenAI, The sharp factor-of-IID threshold for the free Ising model on regular trees, OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 236; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-sharp-factor-of-IID-threshold-for-the-free-Ising-model-on-regular-trees-September-26-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/FreeIsing/Ising/StrictFactorRecovery.lean (declaration OAI.Problem367.IsingObservationFactor.siteVariance_eq_zero_of_subcritical_actual_variance_identity)

import Mathlib
import Mathlib.MeasureTheory.Integral.Marginal
import Definitions.Def_FreeIsing
import Definitions.Def_Q243FI000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal

namespace Problem367.IsingObservationFactor

open IsingObservationInnovation IsingCopySmallLogLoss
open ConnectedHull

variable {d : ℕ} {beta : ℝ}
variable {μ : Measure (TreeVertex d → IsingSpin)} [IsProbabilityMeasure μ]

theorem siteVariance_eq_zero_of_subcritical_actual_variance_identity
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (hstrict : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 < 1) (T : ℝ≥0)
    (hAC : AbsolutelyContinuousOnInterval
      (fun t : ℝ => siteVariance beta μ (root d) t.toNNReal) 0 (T : ℝ))
    (hderiv : ∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) (T : ℝ)),
      deriv (fun s : ℝ => siteVariance beta μ (root d) s.toNNReal) t =
        ∫ q, IsingCopyEnergy.density beta (root d) t q ∂copies beta μ) :
    ∀ t : ℝ≥0, t ≤ T → siteVariance beta μ (root d) t = 0 := by
  sorry

end Problem367.IsingObservationFactor

end

end OAI
end
