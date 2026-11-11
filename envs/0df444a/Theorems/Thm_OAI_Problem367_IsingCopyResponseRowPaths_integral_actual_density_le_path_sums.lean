-- Prove2me | Theorems.Thm_OAI_Problem367_IsingCopyResponseRowPaths_integral_actual_density_le_path_sums
-- name    : OAI.Problem367.IsingCopyResponseRowPaths.integral_actual_density_le_path_sums
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T01:42:58.205038+00:00
-- url     : https://prove2.me/theorems/348d457a-8e0f-423f-bc42-92e49676d033
-- title:
--   OAI.Problem367.IsingCopyResponseRowPaths.integral_actual_density_le_path_sums: intermediate lemma from OpenAI, The sharp factor-of-IID threshold for the free Ising model on regular trees
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Problem367.free_ising_factor_iff_threshold`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The sharp factor-of-IID threshold for the free Ising model on regular trees*, OpenAI Math Release, September 26, 2026, result family 236, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Problem367.IsingCopyResponseRowPaths.integral_actual_density_le_path_sums` of [lean/OAI/Probability/FreeIsing/Ising/CopySpatialEndpoints.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/FreeIsing/Ising/CopySpatialEndpoints.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Problem367.IsingCopyResponseRowPaths`, with `open MeasureTheory ProbabilityTheory`, `open scoped NNReal`, `open IsingObservationInnovation IsingObservationFactor IsingCopySpectral`, `open IsingCopyStationarity IsingConditionalCopyBounds ConnectedHull`):
--
--   ```lean
--   theorem integral_actual_density_le_path_sums
--       (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
--       {t : ℝ≥0} (ht : 0 < t)
--       (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1)
--       (hQ : Summable (noiseShellEnergy (μ := μ) hb t))
--       (hL : Summable (linearShellEnergy (μ := μ) hb t))
--       (hZ : Summable (fun n => Real.sqrt (noiseShellEnergy (μ := μ) hb t n))) :
--       Integrable (IsingCopyEnergy.density beta (root d) t) (copies beta μ) ∧
--       (∫ q, IsingCopyEnergy.density beta (root d) t q ∂copies beta μ) ≤
--         (2 + 8 * ((d : ℝ) * Real.tanh beta ^ 2)) *
--           ((∫ q, (fieldDifference beta (root d) t q) ^ 2 ∂copies beta μ) +
--             (∑' n, noiseShellEnergy (μ := μ) hb t n) +
--             (∑' n, linearShellEnergy (μ := μ) hb t n) +
--             Real.sqrt (∫ q, (fieldDifference beta (root d) t q) ^ 2 ∂copies beta μ) *
--               (∑' n, Real.sqrt (noiseShellEnergy (μ := μ) hb t n)))
--   ```
--
--   **Definitions.** The statement is written with `OAI.Problem367.ConnectedHull.root`, `OAI.Problem367.IsingConditionalCopyBounds.fieldDifference`, `OAI.Problem367.IsingCopyEnergy.Joint`, `OAI.Problem367.IsingCopyEnergy.density`, `OAI.Problem367.IsingObservationFactor.copies`, `OAI.Problem367.IsingObservationInnovation.Paths`, `OAI.Problem367.WienerSampler.Path` and `OAI.Problem367.WienerSampler.pathMeasurableSpace` (definitions bundle `Q243FI000` of this split); `OAI.Problem367.IsingCopyResponseRowPaths.linearShellEnergy` and `OAI.Problem367.IsingCopyResponseRowPaths.noiseShellEnergy` (definitions bundle `Q243FI004` of this split); `OAI.Problem367.HasFreeIsingLaw`, `OAI.Problem367.IsingSpin`, `OAI.Problem367.TreeVertex` and `OAI.Problem367.isingSpinMeasurable` (the published bundle `Def_FreeIsing`).
--
--   **Used by.** The proof of `OAI.Problem367.IsingCopyResponseRowPaths.exists_actual_spatial_endpoint_constant` of this split imports it.
-- source:
--   OpenAI, The sharp factor-of-IID threshold for the free Ising model on regular trees, OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 236; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-sharp-factor-of-IID-threshold-for-the-free-Ising-model-on-regular-trees-September-26-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/FreeIsing/Ising/CopySpatialEndpoints.lean (declaration OAI.Problem367.IsingCopyResponseRowPaths.integral_actual_density_le_path_sums)

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
open IsingObservationInnovation IsingObservationFactor IsingCopySpectral
open IsingCopyStationarity IsingConditionalCopyBounds ConnectedHull

variable {d : ℕ} {beta : ℝ}
variable {μ : Measure (TreeVertex d → IsingSpin)} [IsProbabilityMeasure μ]

theorem integral_actual_density_le_path_sums
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    {t : ℝ≥0} (ht : 0 < t)
    (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1)
    (hQ : Summable (noiseShellEnergy (μ := μ) hb t))
    (hL : Summable (linearShellEnergy (μ := μ) hb t))
    (hZ : Summable (fun n => Real.sqrt (noiseShellEnergy (μ := μ) hb t n))) :
    Integrable (IsingCopyEnergy.density beta (root d) t) (copies beta μ) ∧
    (∫ q, IsingCopyEnergy.density beta (root d) t q ∂copies beta μ) ≤
      (2 + 8 * ((d : ℝ) * Real.tanh beta ^ 2)) *
        ((∫ q, (fieldDifference beta (root d) t q) ^ 2 ∂copies beta μ) +
          (∑' n, noiseShellEnergy (μ := μ) hb t n) +
          (∑' n, linearShellEnergy (μ := μ) hb t n) +
          Real.sqrt (∫ q, (fieldDifference beta (root d) t q) ^ 2 ∂copies beta μ) *
            (∑' n, Real.sqrt (noiseShellEnergy (μ := μ) hb t n))) := by
  sorry

end Problem367.IsingCopyResponseRowPaths

end

end OAI
end
