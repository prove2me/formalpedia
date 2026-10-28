-- Prove2me | Theorems.Thm_OAI_SKGap_actual_path_bias
-- name    : OAI.SKGap.actual_path_bias
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T06:21:26.948991+00:00
-- url     : https://prove2.me/theorems/ba839198-cefe-4686-b0c9-33bbeb7537df
-- title:
--   OAI.SKGap.actual_path_bias: intermediate lemma from OpenAI, A spectral gap throughout the high-temperature Sherrington-Kirkpatrick phase (result family 227)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SKGap.sk_main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A spectral gap throughout the high-temperature Sherrington-Kirkpatrick phase (result family 227)*, OpenAI Math Release, September 24, 2026, result family 227, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SKGap.actual_path_bias` of [lean/OAI/Probability/SKGap/Brownian/PathBias.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/SKGap/Brownian/PathBias.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SKGap`, with `open Matrix MeasureTheory ProbabilityTheory Real Set Filter`, `open RealComplex`, `open scoped BigOperators Matrix.Norms.Frobenius NNReal ENNReal SchwartzMap Topology`):
--
--   ```lean
--   theorem actual_path_bias {j A : ℝ} (hj : 0 < j) (hA : 0 < A) (hs : sqrt j*A < 1) :
--       ∃ (f : 𝓢(ℝ,ℂ)) (R : ℝ) (hR : 0 ≤ R) (lo hi C : ℝ) (N : ℕ),
--         R = 2*sqrt j+1+1 ∧ lo = (1-sqrt j*A)^2/4 ∧ hi = 2+A*(2*sqrt j+1+j*A) ∧
--         0 < lo ∧ (∀ x ∈ Icc lo hi, f x=(x:ℂ)⁻¹) ∧ (∀ x, star (f x)=f x) ∧
--         0 < C ∧ 0 < N ∧
--         (∀ (n : ℕ), N ≤ n → ∀ (a : Fin n → ℝ), (∀ i, 0 ≤ a i) →
--           (∀ i, a i ≤ A) → ∀ z ∈ Icc (0:ℝ) 1, ∀ i,
--             |pathExpected f R hR j a z i-1| ≤ C/(n:ℝ))
--   ```
--
--   **Definitions.** The statement is written with `OAI.SKGap.pathExpected` (definitions bundle `OAIQ072A000` of this split).
--
--   **Used by.** The proof of `OAI.SKGap.actual_projected_path_equivalents` of this split imports it.
-- source:
--   OpenAI, A spectral gap throughout the high-temperature Sherrington-Kirkpatrick phase (result family 227), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 227; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/A-spectral-gap-throughout-the-high-temperature-Sherrington-Kirkpatrick-phase-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/SKGap/Brownian/PathBias.lean (declaration OAI.SKGap.actual_path_bias)

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
open scoped BigOperators Matrix.Norms.Frobenius NNReal ENNReal SchwartzMap Topology

theorem actual_path_bias {j A : ℝ} (hj : 0 < j) (hA : 0 < A) (hs : sqrt j*A < 1) :
    ∃ (f : 𝓢(ℝ,ℂ)) (R : ℝ) (hR : 0 ≤ R) (lo hi C : ℝ) (N : ℕ),
      R = 2*sqrt j+1+1 ∧ lo = (1-sqrt j*A)^2/4 ∧ hi = 2+A*(2*sqrt j+1+j*A) ∧
      0 < lo ∧ (∀ x ∈ Icc lo hi, f x=(x:ℂ)⁻¹) ∧ (∀ x, star (f x)=f x) ∧
      0 < C ∧ 0 < N ∧
      (∀ (n : ℕ), N ≤ n → ∀ (a : Fin n → ℝ), (∀ i, 0 ≤ a i) →
        (∀ i, a i ≤ A) → ∀ z ∈ Icc (0:ℝ) 1, ∀ i,
          |pathExpected f R hR j a z i-1| ≤ C/(n:ℝ)) := by
  sorry
end SKGap
end
end

end OAI
end
