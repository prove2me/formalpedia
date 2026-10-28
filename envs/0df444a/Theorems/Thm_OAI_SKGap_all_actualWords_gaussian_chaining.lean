-- Prove2me | Theorems.Thm_OAI_SKGap_all_actualWords_gaussian_chaining
-- name    : OAI.SKGap.all_actualWords_gaussian_chaining
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T06:22:17.200075+00:00
-- url     : https://prove2.me/theorems/c9222f1b-ec48-4f11-bc86-003ca4afe925
-- title:
--   OAI.SKGap.all_actualWords_gaussian_chaining: intermediate lemma from OpenAI, A spectral gap throughout the high-temperature Sherrington-Kirkpatrick phase (result family 227)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SKGap.sk_main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A spectral gap throughout the high-temperature Sherrington-Kirkpatrick phase (result family 227)*, OpenAI Math Release, September 24, 2026, result family 227, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SKGap.all_actualWords_gaussian_chaining` of [lean/OAI/Probability/SKGap/Matrix/WordTemplateSurjective.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/SKGap/Matrix/WordTemplateSurjective.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SKGap`, with `open Matrix Real Set MeasureTheory ProbabilityTheory Filter`, `open scoped BigOperators Matrix.Norms.Frobenius SchwartzMap Topology`):
--
--   ```lean
--   theorem all_actualWords_gaussian_chaining (f : 𝓢(ℝ,ℂ)) {R j A D : ℝ}
--       (hR : 0 ≤ R) (hj : 0 ≤ j) (hA : 0<A) (hD : 0<D) (L : ℕ) :
--       ∃ C : ℝ,0<C ∧ ∀ n : ℕ,1 ≤ n→∀ p : Bool,
--       (Measure.pi (fun _ : MatrixCoordinates (Fin n)=>gaussianReal 0 1))
--         {g | ∃ (a : Fin n→ℝ) (F : List (WordLetter (Fin n))),
--           (∀ i,a i∈Icc 0 A) ∧ F.length ≤ L ∧ (∀ l∈F,l.bounded D) ∧
--           C< matrixWordSeminorm p
--           (matrixCentered (fun x : EuclideanSpace ℝ (MatrixCoordinates (Fin n))=>
--             actualWord f R hR j a 1 F (goeMatrix (j/n) x)) (WithLp.toLp 2 g))} ≤
--         (wordPatternSet L L).card*ENNReal.ofReal (3*exp (-(n:ℝ)))
--   ```
--
--   **Definitions.** The statement is written with `OAI.SKGap.MatrixCoordinates`, `OAI.SKGap.WordLetter`, `OAI.SKGap.WordTemplateLetter`, `OAI.SKGap.actualWord`, `OAI.SKGap.goeMatrix`, `OAI.SKGap.matrixCentered`, `OAI.SKGap.matrixWordSeminorm`, `OAI.SKGap.wordPatternSet` and `OAI.SKGap.WordLetter.bounded` (definitions bundle `OAIQ072A000` of this split).
--
--   **Used by.** The proof of `OAI.SKGap.actual_word_simultaneous_prediction_of_cutoff` of this split imports it.
-- source:
--   OpenAI, A spectral gap throughout the high-temperature Sherrington-Kirkpatrick phase (result family 227), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 227; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/A-spectral-gap-throughout-the-high-temperature-Sherrington-Kirkpatrick-phase-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/SKGap/Matrix/WordTemplateSurjective.lean (declaration OAI.SKGap.all_actualWords_gaussian_chaining)

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

theorem all_actualWords_gaussian_chaining (f : 𝓢(ℝ,ℂ)) {R j A D : ℝ}
    (hR : 0 ≤ R) (hj : 0 ≤ j) (hA : 0<A) (hD : 0<D) (L : ℕ) :
    ∃ C : ℝ,0<C ∧ ∀ n : ℕ,1 ≤ n→∀ p : Bool,
    (Measure.pi (fun _ : MatrixCoordinates (Fin n)=>gaussianReal 0 1))
      {g | ∃ (a : Fin n→ℝ) (F : List (WordLetter (Fin n))),
        (∀ i,a i∈Icc 0 A) ∧ F.length ≤ L ∧ (∀ l∈F,l.bounded D) ∧
        C< matrixWordSeminorm p
        (matrixCentered (fun x : EuclideanSpace ℝ (MatrixCoordinates (Fin n))=>
          actualWord f R hR j a 1 F (goeMatrix (j/n) x)) (WithLp.toLp 2 g))} ≤
      (wordPatternSet L L).card*ENNReal.ofReal (3*exp (-(n:ℝ))) := by
  sorry
end SKGap
end
end

end OAI
end
