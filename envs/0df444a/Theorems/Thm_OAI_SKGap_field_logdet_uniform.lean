-- Prove2me | Theorems.Thm_OAI_SKGap_field_logdet_uniform
-- name    : OAI.SKGap.field_logdet_uniform
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T06:22:27.156674+00:00
-- url     : https://prove2.me/theorems/911af080-380f-45c4-b6d0-0ce6ce6ad3e4
-- title:
--   OAI.SKGap.field_logdet_uniform: intermediate lemma from OpenAI, A spectral gap throughout the high-temperature Sherrington-Kirkpatrick phase (result family 227)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SKGap.sk_main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A spectral gap throughout the high-temperature Sherrington-Kirkpatrick phase (result family 227)*, OpenAI Math Release, September 24, 2026, result family 227, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SKGap.field_logdet_uniform` of [lean/OAI/Probability/SKGap/Stability/FieldLogDet.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/SKGap/Stability/FieldLogDet.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SKGap`, with `open Matrix Real Set MeasureTheory ProbabilityTheory GaussianDensity`, `open scoped BigOperators Matrix.Norms.Frobenius ENNReal`):
--
--   ```lean
--   theorem field_logdet_uniform {j ε : ℝ} (hj : 0 < j) (hj1 : j < 1) (hε : 0 < ε) :
--       ∃ γ : ℝ,0 < γ ∧ ∃ N : ℕ,0 < N ∧ ∀ n : ℕ,N ≤ n →
--       (gaussianCoordinates (MatrixCoordinates (Fin n))).real
--         {g | ∃ y : Field n,(n:ℝ)*(j*varianceAverage y^2+ε) <
--           log ((fieldJacobian j (plantedInteraction j (goeMatrix (j/(n:ℝ)) g)) y)ᵀ*
--             fieldJacobian j (plantedInteraction j (goeMatrix (j/(n:ℝ)) g)) y+γ • 1).det} ≤
--         4*exp (-min 1 (1/(π^2*j))*(n:ℝ))
--   ```
--
--   **Definitions.** The statement is written with `OAI.SKGap.Field`, `OAI.SKGap.MatrixCoordinates`, `OAI.SKGap.fieldJacobian`, `OAI.SKGap.gaussianCoordinates`, `OAI.SKGap.goeMatrix`, `OAI.SKGap.plantedInteraction` and `OAI.SKGap.varianceAverage` (definitions bundle `OAIQ072A000` of this split).
--
--   **Used by.** The proofs of `OAI.SKGap.ObservationBridge.annealed_fixed_time_root_stability` and `OAI.SKGap.positive_time_root_stability` of this split import it.
-- source:
--   OpenAI, A spectral gap throughout the high-temperature Sherrington-Kirkpatrick phase (result family 227), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 227; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/A-spectral-gap-throughout-the-high-temperature-Sherrington-Kirkpatrick-phase-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/SKGap/Stability/FieldLogDet.lean (declaration OAI.SKGap.field_logdet_uniform)

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

theorem field_logdet_uniform {j ε : ℝ} (hj : 0 < j) (hj1 : j < 1) (hε : 0 < ε) :
    ∃ γ : ℝ,0 < γ ∧ ∃ N : ℕ,0 < N ∧ ∀ n : ℕ,N ≤ n →
    (gaussianCoordinates (MatrixCoordinates (Fin n))).real
      {g | ∃ y : Field n,(n:ℝ)*(j*varianceAverage y^2+ε) <
        log ((fieldJacobian j (plantedInteraction j (goeMatrix (j/(n:ℝ)) g)) y)ᵀ*
          fieldJacobian j (plantedInteraction j (goeMatrix (j/(n:ℝ)) g)) y+γ • 1).det} ≤
      4*exp (-min 1 (1/(π^2*j))*(n:ℝ)) := by
  sorry
end SKGap
end
end

end OAI
end
