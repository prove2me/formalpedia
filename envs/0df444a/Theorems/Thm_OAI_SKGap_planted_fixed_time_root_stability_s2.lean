-- Prove2me | Theorems.Thm_OAI_SKGap_planted_fixed_time_root_stability_s2
-- name    : OAI.SKGap.planted_fixed_time_root_stability_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T10:48:34.523145+00:00
-- url     : https://prove2.me/theorems/32d0d901-656e-46fa-b341-b795ba2ec962
-- title:
--   OAI.SKGap.planted_fixed_time_root_stability_s2: intermediate lemma from OpenAI, Critical mixing in the Sherrington-Kirkpatrick model (result family 227)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CriticalSK.critical_mixing_bounds`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Critical mixing in the Sherrington-Kirkpatrick model (result family 227)*, OpenAI Math Release, September 25, 2026, result family 227, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SKGap`, with `open Matrix Real Set MeasureTheory ProbabilityTheory GaussianDensity`, `open scoped BigOperators ENNReal`):
--
--   ```lean
--   theorem planted_fixed_time_root_stability_s2 {j T : ℝ} (hj : 0 < j) (hj1 : j < 1)
--       (hT : 0 < T) :
--       ∃ A K ε c ρ a : ℝ,1 < A ∧ 2*sqrt j < K ∧ sqrt j*A < 1 ∧
--         0 < ε ∧ 0 < c ∧ 0 < ρ ∧ 0 < a ∧ ∃ N : ℕ,0 < N ∧
--       ∀ n : ℕ,N ≤ n → ∀ t ∈ Icc 0 T,
--         ((gaussianCoordinates (MatrixCoordinates (Fin n))).prod
--           (Measure.pi (fun _ : Fin n=>gaussianReal 0 t.toNNReal))).real
--           (plantedRootBad n j A K ε c ρ t) ≤ exp (-a*(n:ℝ))
--   ```
--
--   **Definitions.** The statement is written with `OAI.SKGap.MatrixCoordinates`, `OAI.SKGap.gaussianCoordinates` and `OAI.SKGap.plantedRootBad` (definitions bundle `OAIQ072A000` of this split).
--
--   **Used by.** No other item of this split imports it.
-- source:
--   OpenAI, Critical mixing in the Sherrington-Kirkpatrick model (result family 227), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 227; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Critical-mixing-in-the-Sherrington-Kirkpatrick-model-September-25-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ072A000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix Real Set MeasureTheory ProbabilityTheory GaussianDensity
open scoped BigOperators ENNReal

theorem planted_fixed_time_root_stability_s2 {j T : ℝ} (hj : 0 < j) (hj1 : j < 1)
    (hT : 0 < T) :
    ∃ A K ε c ρ a : ℝ,1 < A ∧ 2*sqrt j < K ∧ sqrt j*A < 1 ∧
      0 < ε ∧ 0 < c ∧ 0 < ρ ∧ 0 < a ∧ ∃ N : ℕ,0 < N ∧
    ∀ n : ℕ,N ≤ n → ∀ t ∈ Icc 0 T,
      ((gaussianCoordinates (MatrixCoordinates (Fin n))).prod
        (Measure.pi (fun _ : Fin n=>gaussianReal 0 t.toNNReal))).real
        (plantedRootBad n j A K ε c ρ t) ≤ exp (-a*(n:ℝ)) := by
  sorry
end SKGap
end
end

end OAI
end
