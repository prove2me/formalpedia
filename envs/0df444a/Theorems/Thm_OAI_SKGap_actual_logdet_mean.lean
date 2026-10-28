-- Prove2me | Theorems.Thm_OAI_SKGap_actual_logdet_mean
-- name    : OAI.SKGap.actual_logdet_mean
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T06:19:35.812535+00:00
-- url     : https://prove2.me/theorems/5a49ae9a-1d3f-497a-a1b9-1da666ce88b2
-- title:
--   OAI.SKGap.actual_logdet_mean: intermediate lemma from OpenAI, A spectral gap throughout the high-temperature Sherrington-Kirkpatrick phase (result family 227)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SKGap.sk_main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A spectral gap throughout the high-temperature Sherrington-Kirkpatrick phase (result family 227)*, OpenAI Math Release, September 24, 2026, result family 227, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SKGap.actual_logdet_mean` of [lean/OAI/Probability/SKGap/Stability/LogDetUniformMean.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/SKGap/Stability/LogDetUniformMean.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SKGap`, with `open Matrix MeasureTheory ProbabilityTheory Real Set Filter`, `open RealComplex`, `open scoped BigOperators Matrix.Norms.Frobenius SchwartzMap Topology`):
--
--   ```lean
--   theorem actual_logdet_mean {j : ℝ} (hj : 0 < j) (hj1 : j < 1) :
--       ∃ B : ℝ, 0 ≤ B ∧ ∀ γ : ℝ, 0 < γ → ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, 0 < N ∧
--         ∀ n : ℕ, N ≤ n → ∀ a : Fin n → ℝ, (∀ i, 0 ≤ a i) → (∀ i, a i ≤ 1) →
--           (∫ g, LogDet.regularizedLogDet γ (logPath ((j/(n:ℝ))*∑ i,a i) a
--             (goeMatrix (j/(n:ℝ)) g) 1)
--             ∂Measure.pi (fun _ : MatrixCoordinates (Fin n) => gaussianReal 0 1)) ≤
--             j*((∑ i,a i)/(n:ℝ))^2+γ*B^2+C/(n:ℝ)
--   ```
--
--   **Definitions.** The statement is written with `OAI.SKGap.MatrixCoordinates`, `OAI.SKGap.goeMatrix`, `OAI.SKGap.logPath` and `OAI.SKGap.LogDet.regularizedLogDet` (definitions bundle `OAIQ072A000` of this split).
--
--   **Used by.** The proof of `OAI.SKGap.field_logdet_uniform` of this split imports it.
-- source:
--   OpenAI, A spectral gap throughout the high-temperature Sherrington-Kirkpatrick phase (result family 227), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 227; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/A-spectral-gap-throughout-the-high-temperature-Sherrington-Kirkpatrick-phase-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/SKGap/Stability/LogDetUniformMean.lean (declaration OAI.SKGap.actual_logdet_mean)

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
open Matrix MeasureTheory ProbabilityTheory Real Set Filter
open RealComplex
open scoped BigOperators Matrix.Norms.Frobenius SchwartzMap Topology

theorem actual_logdet_mean {j : ℝ} (hj : 0 < j) (hj1 : j < 1) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ γ : ℝ, 0 < γ → ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, 0 < N ∧
      ∀ n : ℕ, N ≤ n → ∀ a : Fin n → ℝ, (∀ i, 0 ≤ a i) → (∀ i, a i ≤ 1) →
        (∫ g, LogDet.regularizedLogDet γ (logPath ((j/(n:ℝ))*∑ i,a i) a
          (goeMatrix (j/(n:ℝ)) g) 1)
          ∂Measure.pi (fun _ : MatrixCoordinates (Fin n) => gaussianReal 0 1)) ≤
          j*((∑ i,a i)/(n:ℝ))^2+γ*B^2+C/(n:ℝ) := by
  sorry
end SKGap
end
end

end OAI
end
