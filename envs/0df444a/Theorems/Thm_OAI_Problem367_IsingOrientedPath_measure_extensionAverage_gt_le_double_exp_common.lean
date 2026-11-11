-- Prove2me | Theorems.Thm_OAI_Problem367_IsingOrientedPath_measure_extensionAverage_gt_le_double_exp_common
-- name    : OAI.Problem367.IsingOrientedPath.measure_extensionAverage_gt_le_double_exp_common
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T01:43:31.333004+00:00
-- url     : https://prove2.me/theorems/14f58709-fe4f-4160-bf87-d422cf1363f4
-- title:
--   OAI.Problem367.IsingOrientedPath.measure_extensionAverage_gt_le_double_exp_common: intermediate lemma from OpenAI, The sharp factor-of-IID threshold for the free Ising model on regular trees
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Problem367.free_ising_factor_iff_threshold`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The sharp factor-of-IID threshold for the free Ising model on regular trees*, OpenAI Math Release, September 26, 2026, result family 236, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Problem367.IsingOrientedPath.measure_extensionAverage_gt_le_double_exp_common` of [lean/OAI/Probability/FreeIsing/Ising/OrientedStemTail.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/FreeIsing/Ising/OrientedStemTail.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Problem367.IsingOrientedPath`, with `open MeasureTheory`, `open scoped NNReal`, `open IsingObservationInnovation TreeOrbitAverage`):
--
--   ```lean
--   theorem measure_extensionAverage_gt_le_double_exp_common
--       (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta) (hd : 3 ≤ d)
--       (hcritical : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 = 1)
--       {t : ℝ≥0} (ht : 0 < t) (inward : Bool)
--       (stem : List (Fin d)) (hstem : stem.IsChain (· ≠ ·)) (k L : ℕ)
--       {η ℓ : ℝ} (hη0 : 0 ≤ η) (hℓ : 0 ≤ ℓ)
--       (hη : η ≤ ComponentSignalAttenuation.lossCoefficient (Real.tanh beta) / 4)
--       (hηlog : η ≤ Real.log ((d : ℝ) - 1) / 8)
--       (hlevel : ℓ / 2 - 1 ≤ (k + 1 : ℕ)) (htail : ℓ / 2 ≤ (L : ℝ))
--       (hlength : 8 * Real.log 2 ≤
--         ComponentSignalAttenuation.lossCoefficient (Real.tanh beta) *
--           (min (Real.sqrt (t : ℝ)) 1 * ℓ)) :
--       (observationLaw μ) {x | Real.exp (4 * beta / (1 - Real.tanh beta)) *
--         Real.exp (-(η * min (Real.sqrt (t : ℝ)) 1) * ℓ) <
--           extensionAverage hb t inward stem (k + 1 + L) x} ≤
--         ENNReal.ofReal (Real.exp (-(((d : ℝ) - 1) ^ (ℓ / 4)) /
--           (2 * ((d : ℝ) - 1))))
--   ```
--
--   **Definitions.** The statement is written with `OAI.Problem367.IsingObservationInnovation.Paths`, `OAI.Problem367.IsingObservationInnovation.observationLaw`, `OAI.Problem367.WienerSampler.Path` and `OAI.Problem367.WienerSampler.pathMeasurableSpace` (definitions bundle `Q243FI000` of this split); `OAI.Problem367.ComponentSignalAttenuation.lossCoefficient` (definitions bundle `Q243FI001` of this split); `OAI.Problem367.IsingOrientedPath.extensionAverage` (definitions bundle `Q243FI004` of this split); `OAI.Problem367.HasFreeIsingLaw`, `OAI.Problem367.IsingSpin`, `OAI.Problem367.TreeVertex` and `OAI.Problem367.isingSpinMeasurable` (the published bundle `Def_FreeIsing`).
--
--   **Used by.** The proof of `OAI.Problem367.IsingCopyResponseRowPaths.exists_noise_energy_long_constants` of this split imports it.
-- source:
--   OpenAI, The sharp factor-of-IID threshold for the free Ising model on regular trees, OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 236; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-sharp-factor-of-IID-threshold-for-the-free-Ising-model-on-regular-trees-September-26-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/FreeIsing/Ising/OrientedStemTail.lean (declaration OAI.Problem367.IsingOrientedPath.measure_extensionAverage_gt_le_double_exp_common)

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
open MeasureTheory
open scoped NNReal

namespace Problem367.IsingOrientedPath
open IsingObservationInnovation TreeOrbitAverage

variable {d : ℕ} {beta : ℝ}
variable {μ : Measure (TreeVertex d → IsingSpin)} [IsProbabilityMeasure μ]

theorem measure_extensionAverage_gt_le_double_exp_common
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta) (hd : 3 ≤ d)
    (hcritical : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 = 1)
    {t : ℝ≥0} (ht : 0 < t) (inward : Bool)
    (stem : List (Fin d)) (hstem : stem.IsChain (· ≠ ·)) (k L : ℕ)
    {η ℓ : ℝ} (hη0 : 0 ≤ η) (hℓ : 0 ≤ ℓ)
    (hη : η ≤ ComponentSignalAttenuation.lossCoefficient (Real.tanh beta) / 4)
    (hηlog : η ≤ Real.log ((d : ℝ) - 1) / 8)
    (hlevel : ℓ / 2 - 1 ≤ (k + 1 : ℕ)) (htail : ℓ / 2 ≤ (L : ℝ))
    (hlength : 8 * Real.log 2 ≤
      ComponentSignalAttenuation.lossCoefficient (Real.tanh beta) *
        (min (Real.sqrt (t : ℝ)) 1 * ℓ)) :
    (observationLaw μ) {x | Real.exp (4 * beta / (1 - Real.tanh beta)) *
      Real.exp (-(η * min (Real.sqrt (t : ℝ)) 1) * ℓ) <
        extensionAverage hb t inward stem (k + 1 + L) x} ≤
      ENNReal.ofReal (Real.exp (-(((d : ℝ) - 1) ^ (ℓ / 4)) /
        (2 * ((d : ℝ) - 1)))) := by
  sorry

end Problem367.IsingOrientedPath

end

end OAI
end
