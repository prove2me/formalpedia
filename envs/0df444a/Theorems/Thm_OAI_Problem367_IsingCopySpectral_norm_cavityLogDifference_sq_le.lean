-- Prove2me | Theorems.Thm_OAI_Problem367_IsingCopySpectral_norm_cavityLogDifference_sq_le
-- name    : OAI.Problem367.IsingCopySpectral.norm_cavityLogDifference_sq_le
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T01:45:00.948651+00:00
-- url     : https://prove2.me/theorems/f16bd4d9-eabb-429a-ace5-109496c328c2
-- title:
--   OAI.Problem367.IsingCopySpectral.norm_cavityLogDifference_sq_le: intermediate lemma from OpenAI, The sharp factor-of-IID threshold for the free Ising model on regular trees
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Problem367.free_ising_factor_iff_threshold`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The sharp factor-of-IID threshold for the free Ising model on regular trees*, OpenAI Math Release, September 26, 2026, result family 236, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Problem367.IsingCopySpectral.norm_cavityLogDifference_sq_le` of [lean/OAI/Probability/FreeIsing/Ising/CopyObservables.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/FreeIsing/Ising/CopyObservables.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Problem367.IsingCopySpectral`, with `open MeasureTheory ProbabilityTheory`, `open scoped NNReal`, `open IsingObservationInnovation IsingObservationFactor IsingCopyStationarity PlantedSymmetry`):
--
--   ```lean
--   theorem norm_cavityLogDifference_sq_le
--       (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
--       (t : ℝ≥0) (o v w : TreeVertex d) :
--       ‖observableDifference (beta := beta) (memLp_cavityLogObservable hμ hbeta t v w)‖ ^ 2 ≤
--         cavityLogVarianceCoefficient (Real.tanh beta) *
--           ∫ q, (IsingConditionalCopyBounds.fieldDifference beta o t q) ^ 2 ∂copies beta μ
--   ```
--
--   **Definitions.** The statement is written with `OAI.Problem367.IsingConditionalCopyBounds.fieldDifference`, `OAI.Problem367.IsingObservationFactor.copies`, `OAI.Problem367.IsingObservationInnovation.Paths`, `OAI.Problem367.WienerSampler.Path` and `OAI.Problem367.WienerSampler.pathMeasurableSpace` (definitions bundle `Q243FI000` of this split); `OAI.Problem367.cavityLogVarianceCoefficient` (definitions bundle `Q243FI001` of this split); `OAI.Problem367.IsingCopySpectral.cavityLogObservable` (definitions bundle `Q243FI004` of this split); `OAI.Problem367.IsingCopySpectral.differenceSpace`, `OAI.Problem367.IsingCopySpectral.memLp_cavityLogObservable` and `OAI.Problem367.IsingCopySpectral.observableDifference` (definitions bundle `Q243FI005` of this split); `OAI.Problem367.HasFreeIsingLaw`, `OAI.Problem367.IsingSpin`, `OAI.Problem367.TreeVertex` and `OAI.Problem367.isingSpinMeasurable` (the published bundle `Def_FreeIsing`).
--
--   **Used by.** The proofs of `OAI.Problem367.IsingCopyResponseRowPaths.exists_actual_spatial_endpoint_constant` and `OAI.Problem367.IsingObservationFactor.siteVariance_eq_zero_of_subcritical_actual_variance_identity` of this split import it.
-- source:
--   OpenAI, The sharp factor-of-IID threshold for the free Ising model on regular trees, OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 236; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-sharp-factor-of-IID-threshold-for-the-free-Ising-model-on-regular-trees-September-26-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/FreeIsing/Ising/CopyObservables.lean (declaration OAI.Problem367.IsingCopySpectral.norm_cavityLogDifference_sq_le)

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
open IsingObservationInnovation IsingObservationFactor IsingCopyStationarity PlantedSymmetry

variable {d : ℕ} {beta : ℝ}
variable {μ : Measure (TreeVertex d → IsingSpin)} [IsProbabilityMeasure μ]

theorem norm_cavityLogDifference_sq_le
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (t : ℝ≥0) (o v w : TreeVertex d) :
    ‖observableDifference (beta := beta) (memLp_cavityLogObservable hμ hbeta t v w)‖ ^ 2 ≤
      cavityLogVarianceCoefficient (Real.tanh beta) *
        ∫ q, (IsingConditionalCopyBounds.fieldDifference beta o t q) ^ 2 ∂copies beta μ := by
  sorry

end Problem367.IsingCopySpectral

end

end OAI
end
