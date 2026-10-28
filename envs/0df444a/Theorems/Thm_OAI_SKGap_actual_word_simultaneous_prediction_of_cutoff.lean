-- Prove2me | Theorems.Thm_OAI_SKGap_actual_word_simultaneous_prediction_of_cutoff
-- name    : OAI.SKGap.actual_word_simultaneous_prediction_of_cutoff
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T06:20:01.319864+00:00
-- url     : https://prove2.me/theorems/a10e549e-602b-4a52-a171-4e11929ce984
-- title:
--   OAI.SKGap.actual_word_simultaneous_prediction_of_cutoff: intermediate lemma from OpenAI, A spectral gap throughout the high-temperature Sherrington-Kirkpatrick phase (result family 227)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SKGap.sk_main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A spectral gap throughout the high-temperature Sherrington-Kirkpatrick phase (result family 227)*, OpenAI Math Release, September 24, 2026, result family 227, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SKGap.actual_word_simultaneous_prediction_of_cutoff` of [lean/OAI/Probability/SKGap/Matrix/WordBiasCutoff.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/SKGap/Matrix/WordBiasCutoff.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SKGap`, with `open Matrix Real Set MeasureTheory ProbabilityTheory Filter`, `open scoped BigOperators Matrix.Norms.Frobenius SchwartzMap Topology`):
--
--   ```lean
--   theorem actual_word_simultaneous_prediction_of_cutoff {j A D : ℝ} (hj : 0<j) (hA : 0<A)
--       (hs : sqrt j*A<1) (hD : 1≤D) (hAD : A≤D) (L : ℕ) (f : 𝓢(ℝ,ℂ))
--       (hf : ∀ x∈Icc ((1-sqrt j*A)^2/4) (2+A*(2*sqrt j+1+j*A)),f x=(x:ℂ)⁻¹)
--       (hR : 0≤2*sqrt j+1+1) :
--       ∃ (C : ℝ) (N : ℕ),0<C ∧ 0<N ∧
--         ∀ n,N≤n → ∀ p : Bool,
--           (Measure.pi (fun _ : MatrixCoordinates (Fin n)=>gaussianReal 0 1))
--           {g | ∃ (a : Fin n→ℝ) (F : List (WordLetter (Fin n))),
--             (∀ i,a i∈Icc 0 A) ∧ F.length≤L ∧ (∀ l∈F,l.bounded D) ∧ inverseCount F≤1 ∧
--             C< matrixWordSeminorm p
--               (actualWord f (2*sqrt j+1+1) hR j a 1 F (goeMatrix (j/n) g)-Matrix.diagonal (wordPrediction j a 1 F))} ≤
--             (wordPatternSet L L).card*ENNReal.ofReal (3*exp (-(n:ℝ)))
--   ```
--
--   **Definitions.** The statement is written with `OAI.SKGap.MatrixCoordinates`, `OAI.SKGap.WordLetter`, `OAI.SKGap.WordTemplateLetter`, `OAI.SKGap.actualWord`, `OAI.SKGap.goeMatrix`, `OAI.SKGap.inverseCount`, `OAI.SKGap.matrixWordSeminorm`, `OAI.SKGap.wordPatternSet`, `OAI.SKGap.wordPrediction` and `OAI.SKGap.WordLetter.bounded` (definitions bundle `OAIQ072A000` of this split).
--
--   **Used by.** The proof of `OAI.SKGap.zeroDiag_exact_word_source_restriction` of this split imports it.
-- source:
--   OpenAI, A spectral gap throughout the high-temperature Sherrington-Kirkpatrick phase (result family 227), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 227; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/A-spectral-gap-throughout-the-high-temperature-Sherrington-Kirkpatrick-phase-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/SKGap/Matrix/WordBiasCutoff.lean (declaration OAI.SKGap.actual_word_simultaneous_prediction_of_cutoff)

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
open Matrix Real Set MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Matrix.Norms.Frobenius SchwartzMap Topology

theorem actual_word_simultaneous_prediction_of_cutoff {j A D : ℝ} (hj : 0<j) (hA : 0<A)
    (hs : sqrt j*A<1) (hD : 1≤D) (hAD : A≤D) (L : ℕ) (f : 𝓢(ℝ,ℂ))
    (hf : ∀ x∈Icc ((1-sqrt j*A)^2/4) (2+A*(2*sqrt j+1+j*A)),f x=(x:ℂ)⁻¹)
    (hR : 0≤2*sqrt j+1+1) :
    ∃ (C : ℝ) (N : ℕ),0<C ∧ 0<N ∧
      ∀ n,N≤n → ∀ p : Bool,
        (Measure.pi (fun _ : MatrixCoordinates (Fin n)=>gaussianReal 0 1))
        {g | ∃ (a : Fin n→ℝ) (F : List (WordLetter (Fin n))),
          (∀ i,a i∈Icc 0 A) ∧ F.length≤L ∧ (∀ l∈F,l.bounded D) ∧ inverseCount F≤1 ∧
          C< matrixWordSeminorm p
            (actualWord f (2*sqrt j+1+1) hR j a 1 F (goeMatrix (j/n) g)-Matrix.diagonal (wordPrediction j a 1 F))} ≤
          (wordPatternSet L L).card*ENNReal.ofReal (3*exp (-(n:ℝ))) := by
  sorry
end SKGap
end
end

end OAI
end
