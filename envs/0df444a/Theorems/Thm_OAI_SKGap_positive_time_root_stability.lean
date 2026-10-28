-- Prove2me | Theorems.Thm_OAI_SKGap_positive_time_root_stability
-- name    : OAI.SKGap.positive_time_root_stability
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T06:24:51.156899+00:00
-- url     : https://prove2.me/theorems/36020225-fb2b-472d-9771-e1ffc85ab3c4
-- title:
--   OAI.SKGap.positive_time_root_stability: intermediate lemma from OpenAI, A spectral gap throughout the high-temperature Sherrington-Kirkpatrick phase (result family 227)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SKGap.sk_main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A spectral gap throughout the high-temperature Sherrington-Kirkpatrick phase (result family 227)*, OpenAI Math Release, September 24, 2026, result family 227, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SKGap.positive_time_root_stability` of [lean/OAI/Probability/SKGap/Stability/PositiveRootStability.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/SKGap/Stability/PositiveRootStability.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SKGap`, with `open Matrix Real Set MeasureTheory ProbabilityTheory GaussianDensity`, `open scoped BigOperators Matrix.Norms.Frobenius ENNReal`):
--
--   ```lean
--   theorem positive_time_root_stability {j A K t₀ T : ℝ} (hj : 0 < j) (hj1 : j < 1)
--       (hA : 1 ≤ A) (hsub : sqrt j*A < 1) (hK : 0 ≤ K)
--       (ht₀ : 0 < t₀) (hT : t₀ ≤ T) :
--       ∃ ε c ρ a : ℝ,0 < ε ∧ 0 < c ∧ 0 < ρ ∧ 0 < a ∧ ∃ N : ℕ,0 < N ∧
--       ∀ (n : ℕ),N ≤ n → ∀ t ∈ Icc t₀ T,
--       ((gaussianCoordinates (MatrixCoordinates (Fin n))).prod
--         (Measure.pi (fun _ : Fin n=>gaussianReal 0 t.toNNReal))).real
--         {p | (∀ z : Field n,vectorNorm (plantedInteraction j (goeMatrix (j/(n:ℝ)) p.1)*ᵥz) ≤ K*vectorNorm z) ∧
--           ∃ y : Field n, vectorNorm (tapField j (plantedInteraction j (goeMatrix (j/(n:ℝ)) p.1))
--             (fun i=>t+p.2 i) y) ≤ ρ*sqrt (n:ℝ) ∧
--             (goeMatrix (j/(n:ℝ)) p.1,y)∈badFieldSet n j A ε c} ≤
--           4*exp (-min 1 (1/(π^2*j))*(n:ℝ))+exp (-a*(n:ℝ))
--   ```
--
--   **Definitions.** The statement is written with `OAI.SKGap.Field`, `OAI.SKGap.MatrixCoordinates`, `OAI.SKGap.badFieldSet`, `OAI.SKGap.gaussianCoordinates`, `OAI.SKGap.goeMatrix`, `OAI.SKGap.plantedInteraction`, `OAI.SKGap.tapField` and `OAI.SKGap.vectorNorm` (definitions bundle `OAIQ072A000` of this split).
--
--   **Used by.** The proof of `OAI.SKGap.ObservationBridge.annealed_fixed_time_root_stability` of this split imports it.
-- source:
--   OpenAI, A spectral gap throughout the high-temperature Sherrington-Kirkpatrick phase (result family 227), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 227; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/A-spectral-gap-throughout-the-high-temperature-Sherrington-Kirkpatrick-phase-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/SKGap/Stability/PositiveRootStability.lean (declaration OAI.SKGap.positive_time_root_stability)

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

theorem positive_time_root_stability {j A K t₀ T : ℝ} (hj : 0 < j) (hj1 : j < 1)
    (hA : 1 ≤ A) (hsub : sqrt j*A < 1) (hK : 0 ≤ K)
    (ht₀ : 0 < t₀) (hT : t₀ ≤ T) :
    ∃ ε c ρ a : ℝ,0 < ε ∧ 0 < c ∧ 0 < ρ ∧ 0 < a ∧ ∃ N : ℕ,0 < N ∧
    ∀ (n : ℕ),N ≤ n → ∀ t ∈ Icc t₀ T,
    ((gaussianCoordinates (MatrixCoordinates (Fin n))).prod
      (Measure.pi (fun _ : Fin n=>gaussianReal 0 t.toNNReal))).real
      {p | (∀ z : Field n,vectorNorm (plantedInteraction j (goeMatrix (j/(n:ℝ)) p.1)*ᵥz) ≤ K*vectorNorm z) ∧
        ∃ y : Field n, vectorNorm (tapField j (plantedInteraction j (goeMatrix (j/(n:ℝ)) p.1))
          (fun i=>t+p.2 i) y) ≤ ρ*sqrt (n:ℝ) ∧
          (goeMatrix (j/(n:ℝ)) p.1,y)∈badFieldSet n j A ε c} ≤
        4*exp (-min 1 (1/(π^2*j))*(n:ℝ))+exp (-a*(n:ℝ)) := by
  sorry
end SKGap
end
end

end OAI
end
