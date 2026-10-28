-- Prove2me | Theorems.Thm_OAI_SKGap_smalltime_bad_integral
-- name    : OAI.SKGap.smalltime_bad_integral
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T06:24:51.025637+00:00
-- url     : https://prove2.me/theorems/2b5ffd8d-04ec-4631-810a-bee358440723
-- title:
--   OAI.SKGap.smalltime_bad_integral: intermediate lemma from OpenAI, A spectral gap throughout the high-temperature Sherrington-Kirkpatrick phase (result family 227)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SKGap.sk_main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A spectral gap throughout the high-temperature Sherrington-Kirkpatrick phase (result family 227)*, OpenAI Math Release, September 24, 2026, result family 227, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SKGap.smalltime_bad_integral` of [lean/OAI/Probability/SKGap/Entropy/BadIntegralEndpoints.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/SKGap/Entropy/BadIntegralEndpoints.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SKGap`, with `open Matrix Real Set MeasureTheory ProbabilityTheory GaussianDensity`, `open scoped BigOperators Matrix.Norms.Frobenius ENNReal`):
--
--   ```lean
--   theorem smalltime_bad_integral {j q₀ : ℝ} (hj : 0 < j) (hj1 : j < 1) (hq₀ : 0 < q₀) :
--       ∃ t₀ σ₀ a : ℝ, 0 < t₀ ∧ 0 < σ₀ ∧ 0 < a ∧ ∃ N : ℕ,
--       ∀ (n : ℕ) [NeZero n],N ≤ n → ∀ t ∈ Icc 0 t₀,∀ σ ∈ Ioc 0 σ₀,
--       (∫⁻ g, ∫⁻ x, fieldIntegral j σ (plantedInteraction j (goeMatrix (j/(n:ℝ)) g))
--           (fun i=>t+x i) {y | q₀ ≤ overlap y}
--         ∂Measure.pi (fun _ : Fin n=>gaussianReal 0 t.toNNReal)
--         ∂gaussianCoordinates (MatrixCoordinates (Fin n))) ≤ ENNReal.ofReal (exp (-a*(n:ℝ)))
--   ```
--
--   **Definitions.** The statement is written with `OAI.SKGap.MatrixCoordinates`, `OAI.SKGap.fieldIntegral`, `OAI.SKGap.gaussianCoordinates`, `OAI.SKGap.goeMatrix`, `OAI.SKGap.overlap` and `OAI.SKGap.plantedInteraction` (definitions bundle `OAIQ072A000` of this split).
--
--   **Used by.** The proof of `OAI.SKGap.ObservationBridge.annealed_fixed_time_root_stability` of this split imports it.
-- source:
--   OpenAI, A spectral gap throughout the high-temperature Sherrington-Kirkpatrick phase (result family 227), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 227; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/A-spectral-gap-throughout-the-high-temperature-Sherrington-Kirkpatrick-phase-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/SKGap/Entropy/BadIntegralEndpoints.lean (declaration OAI.SKGap.smalltime_bad_integral)

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
open scoped BigOperators Matrix.Norms.Frobenius ENNReal

theorem smalltime_bad_integral {j q₀ : ℝ} (hj : 0 < j) (hj1 : j < 1) (hq₀ : 0 < q₀) :
    ∃ t₀ σ₀ a : ℝ, 0 < t₀ ∧ 0 < σ₀ ∧ 0 < a ∧ ∃ N : ℕ,
    ∀ (n : ℕ) [NeZero n],N ≤ n → ∀ t ∈ Icc 0 t₀,∀ σ ∈ Ioc 0 σ₀,
    (∫⁻ g, ∫⁻ x, fieldIntegral j σ (plantedInteraction j (goeMatrix (j/(n:ℝ)) g))
        (fun i=>t+x i) {y | q₀ ≤ overlap y}
      ∂Measure.pi (fun _ : Fin n=>gaussianReal 0 t.toNNReal)
      ∂gaussianCoordinates (MatrixCoordinates (Fin n))) ≤ ENNReal.ofReal (exp (-a*(n:ℝ))) := by
  sorry

end SKGap
end
end

end OAI
end
