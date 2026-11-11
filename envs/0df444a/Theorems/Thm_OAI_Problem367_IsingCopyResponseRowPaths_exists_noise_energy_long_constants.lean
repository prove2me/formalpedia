-- Prove2me | Theorems.Thm_OAI_Problem367_IsingCopyResponseRowPaths_exists_noise_energy_long_constants
-- name    : OAI.Problem367.IsingCopyResponseRowPaths.exists_noise_energy_long_constants
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T01:42:52.920198+00:00
-- url     : https://prove2.me/theorems/8dc6b252-f4ff-4cdb-8674-fec31467e02a
-- title:
--   OAI.Problem367.IsingCopyResponseRowPaths.exists_noise_energy_long_constants: intermediate lemma from OpenAI, The sharp factor-of-IID threshold for the free Ising model on regular trees
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Problem367.free_ising_factor_iff_threshold`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The sharp factor-of-IID threshold for the free Ising model on regular trees*, OpenAI Math Release, September 26, 2026, result family 236, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Problem367.IsingCopyResponseRowPaths.exists_noise_energy_long_constants` of [lean/OAI/Probability/FreeIsing/Ising/CopyNoiseLongBound.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/FreeIsing/Ising/CopyNoiseLongBound.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Problem367.IsingCopyResponseRowPaths`, with `open MeasureTheory ProbabilityTheory`, `open scoped NNReal`, `open IsingObservationInnovation IsingObservationFactor IsingCopySpectral`, `open IsingOrientedPath IsingCopyPathBounds IsingCopySmallLogLoss TreeKoopman`):
--
--   ```lean
--   theorem exists_noise_energy_long_constants
--       (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hd : 3 ≤ d) (hb : 0 ≤ beta)
--       (hcritical : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 = 1) (T : ℝ≥0) :
--       ∃ B E c a q C₀ : ℝ, 0 ≤ B ∧ 0 ≤ E ∧ 0 < c ∧ 0 < a ∧ 1 < q ∧ 0 < C₀ ∧
--         ∀ (t : ℝ≥0), 0 < t → t ≤ T → ∀ (u w : TreeVertex d), treeAdj u w →
--         ∀ v : TreeVertex d, C₀ / min (Real.sqrt (t : ℝ)) 1 ≤ (v.1.length : ℝ) →
--           noiseEnergy (μ := μ) hb t v ≤
--             B * (logVariance hb μ u w t) *
--               ((v.1.length : ℝ) * Real.exp (-(c * min (Real.sqrt (t : ℝ)) 1) * v.1.length)) +
--             E * ((v.1.length : ℝ) ^ 2 * Real.exp (-a * q ^ v.1.length))
--   ```
--
--   **Definitions.** The statement is written with `OAI.Problem367.IsingCopyResponseRowPaths.noiseEnergy` and `OAI.Problem367.IsingCopySmallLogLoss.logVariance` (definitions bundle `Q243FI004` of this split); `OAI.Problem367.HasFreeIsingLaw`, `OAI.Problem367.IsingSpin`, `OAI.Problem367.TreeVertex`, `OAI.Problem367.isingSpinMeasurable` and `OAI.Problem367.treeAdj` (the published bundle `Def_FreeIsing`).
--
--   **Used by.** The proof of `OAI.Problem367.free_ising_factor_below_threshold_of_actual_variance_identity` of this split imports it.
-- source:
--   OpenAI, The sharp factor-of-IID threshold for the free Ising model on regular trees, OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 236; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-sharp-factor-of-IID-threshold-for-the-free-Ising-model-on-regular-trees-September-26-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/FreeIsing/Ising/CopyNoiseLongBound.lean (declaration OAI.Problem367.IsingCopyResponseRowPaths.exists_noise_energy_long_constants)

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
open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace Problem367.IsingCopyResponseRowPaths
open IsingObservationInnovation IsingObservationFactor IsingCopySpectral
open IsingOrientedPath IsingCopyPathBounds IsingCopySmallLogLoss TreeKoopman

variable {d : ℕ} {beta : ℝ}
variable {μ : Measure (TreeVertex d → IsingSpin)} [IsProbabilityMeasure μ]

theorem exists_noise_energy_long_constants
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hd : 3 ≤ d) (hb : 0 ≤ beta)
    (hcritical : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 = 1) (T : ℝ≥0) :
    ∃ B E c a q C₀ : ℝ, 0 ≤ B ∧ 0 ≤ E ∧ 0 < c ∧ 0 < a ∧ 1 < q ∧ 0 < C₀ ∧
      ∀ (t : ℝ≥0), 0 < t → t ≤ T → ∀ (u w : TreeVertex d), treeAdj u w →
      ∀ v : TreeVertex d, C₀ / min (Real.sqrt (t : ℝ)) 1 ≤ (v.1.length : ℝ) →
        noiseEnergy (μ := μ) hb t v ≤
          B * (logVariance hb μ u w t) *
            ((v.1.length : ℝ) * Real.exp (-(c * min (Real.sqrt (t : ℝ)) 1) * v.1.length)) +
          E * ((v.1.length : ℝ) ^ 2 * Real.exp (-a * q ^ v.1.length)) := by
  sorry

end Problem367.IsingCopyResponseRowPaths

end

end OAI
end
