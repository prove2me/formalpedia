-- Prove2me | Theorems.Thm_OAI_SKGap_zeroDiag_exact_word_source_restriction
-- name    : OAI.SKGap.zeroDiag_exact_word_source_restriction
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T06:25:26.352786+00:00
-- url     : https://prove2.me/theorems/92d19ae8-a82e-4b57-8225-e399a563d4f1
-- title:
--   OAI.SKGap.zeroDiag_exact_word_source_restriction: intermediate lemma from OpenAI, A spectral gap throughout the high-temperature Sherrington-Kirkpatrick phase (result family 227)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SKGap.sk_main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A spectral gap throughout the high-temperature Sherrington-Kirkpatrick phase (result family 227)*, OpenAI Math Release, September 24, 2026, result family 227, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SKGap.zeroDiag_exact_word_source_restriction` of [lean/OAI/Probability/SKGap/Matrix/WordDiag.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/SKGap/Matrix/WordDiag.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SKGap`, with `open Matrix Real Set MeasureTheory ProbabilityTheory Filter`, `open RealComplex`, `open scoped BigOperators Matrix.Norms.Frobenius SchwartzMap Topology`):
--
--   ```lean
--   theorem zeroDiag_exact_word_source_restriction {j A D c : ℝ} (hj : 0<j) (hA : 0<A)
--       (hs : sqrt j*A<1) (hD : 1≤D) (hAD : A≤D) (hc : 0 < c) (L : ℕ) :
--       ∃ (C : ℝ) (N : ℕ),0<C ∧ 0<N ∧ ∀ n,N≤n → ∀ p : Bool,
--         (Measure.pi (fun _ : MatrixCoordinates (Fin n)=>gaussianReal 0 1))
--         {g | opNorm (removeDiagonal (goeMatrix (j/n) g))≤2*sqrt j+1+1 ∧
--           ∃ (a : Fin n→ℝ) (F : List (WordLetter (Fin n))),
--             (∀ i,a i∈Icc 0 A) ∧ F.length≤L ∧ (∀ l∈F,l.bounded D) ∧ inverseCount F≤1 ∧
--             (inverseCount F=0 ∨ c≤ComplexSpectral.lowerRayleigh (liftMatrix (stabilityMatrix a 1
--               ((j/(n:ℝ))*∑ b,a b) (removeDiagonal (goeMatrix (j/n) g))))) ∧
--             C< matrixWordSeminorm p
--               (exactWord j a F (removeDiagonal (goeMatrix (j/n) g))-Matrix.diagonal (wordPrediction j a 1 F))} ≤
--         (wordPatternSet L L).card*ENNReal.ofReal (3*exp (-(n:ℝ)))+
--           ENNReal.ofReal (exp (-2*(n:ℝ)/(π^2*(sqrt (2*j))^2)))
--   ```
--
--   **Definitions.** The statement is written with `OAI.SKGap.MatrixCoordinates`, `OAI.SKGap.WordLetter`, `OAI.SKGap.WordTemplateLetter`, `OAI.SKGap.exactWord`, `OAI.SKGap.goeMatrix`, `OAI.SKGap.inverseCount`, `OAI.SKGap.matrixWordSeminorm`, `OAI.SKGap.opNorm`, `OAI.SKGap.removeDiagonal`, `OAI.SKGap.stabilityMatrix`, `OAI.SKGap.wordPatternSet`, `OAI.SKGap.wordPrediction`, `OAI.SKGap.ComplexSpectral.lowerRayleigh`, `OAI.SKGap.RealComplex.liftMatrix` and `OAI.SKGap.WordLetter.bounded` (definitions bundle `OAIQ072A000` of this split).
--
--   **Used by.** The proofs of `OAI.SKGapCutoff.Recipe.disorder_closed_word_event` and `OAI.SKGapCutoff.Recipe.disorder_word_event` of this split import it.
-- source:
--   OpenAI, A spectral gap throughout the high-temperature Sherrington-Kirkpatrick phase (result family 227), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 227; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/A-spectral-gap-throughout-the-high-temperature-Sherrington-Kirkpatrick-phase-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/SKGap/Matrix/WordDiag.lean (declaration OAI.SKGap.zeroDiag_exact_word_source_restriction)

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
open RealComplex
open scoped BigOperators Matrix.Norms.Frobenius SchwartzMap Topology

theorem zeroDiag_exact_word_source_restriction {j A D c : ℝ} (hj : 0<j) (hA : 0<A)
    (hs : sqrt j*A<1) (hD : 1≤D) (hAD : A≤D) (hc : 0 < c) (L : ℕ) :
    ∃ (C : ℝ) (N : ℕ),0<C ∧ 0<N ∧ ∀ n,N≤n → ∀ p : Bool,
      (Measure.pi (fun _ : MatrixCoordinates (Fin n)=>gaussianReal 0 1))
      {g | opNorm (removeDiagonal (goeMatrix (j/n) g))≤2*sqrt j+1+1 ∧
        ∃ (a : Fin n→ℝ) (F : List (WordLetter (Fin n))),
          (∀ i,a i∈Icc 0 A) ∧ F.length≤L ∧ (∀ l∈F,l.bounded D) ∧ inverseCount F≤1 ∧
          (inverseCount F=0 ∨ c≤ComplexSpectral.lowerRayleigh (liftMatrix (stabilityMatrix a 1
            ((j/(n:ℝ))*∑ b,a b) (removeDiagonal (goeMatrix (j/n) g))))) ∧
          C< matrixWordSeminorm p
            (exactWord j a F (removeDiagonal (goeMatrix (j/n) g))-Matrix.diagonal (wordPrediction j a 1 F))} ≤
      (wordPatternSet L L).card*ENNReal.ofReal (3*exp (-(n:ℝ)))+
        ENNReal.ofReal (exp (-2*(n:ℝ)/(π^2*(sqrt (2*j))^2))) := by
  sorry
end SKGap
end
end

end OAI
end
