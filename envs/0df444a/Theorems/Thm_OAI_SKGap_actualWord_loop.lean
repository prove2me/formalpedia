-- Prove2me | Theorems.Thm_OAI_SKGap_actualWord_loop
-- name    : OAI.SKGap.actualWord_loop
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T06:21:09.890028+00:00
-- url     : https://prove2.me/theorems/e94cbac4-3c1c-4d05-87b0-4e096dc8f81d
-- title:
--   OAI.SKGap.actualWord_loop: intermediate lemma from OpenAI, A spectral gap throughout the high-temperature Sherrington-Kirkpatrick phase (result family 227)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SKGap.sk_main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A spectral gap throughout the high-temperature Sherrington-Kirkpatrick phase (result family 227)*, OpenAI Math Release, September 24, 2026, result family 227, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SKGap.actualWord_loop` of [lean/OAI/Probability/SKGap/Matrix/WordLoop.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/SKGap/Matrix/WordLoop.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SKGap`, with `open Matrix Real MeasureTheory ProbabilityTheory Set`, `open RealComplex`, `open scoped BigOperators Matrix.Norms.Frobenius NNReal ENNReal SchwartzMap`):
--
--   ```lean
--   theorem actualWord_loop [Nonempty ι] (f : 𝓢(ℝ,ℂ)) {lo hi : ℝ} (hlo : 0<lo)
--       (hf : ∀ x∈Icc lo hi,f x=(x:ℂ)⁻¹) {R j A D z r : ℝ}
--       (hR : 0≤R) (hj : 0≤j) (hA : 0≤A) (hD : 0≤D) (hr : 0 ≤ r) {a : ι→ℝ}
--       (ha : ∀ i,0≤a i) (haA : ∀ i,a i≤A) (hz : z∈Icc (0:ℝ) 1)
--       (P Q : List (WordLetter ι)) (hP : ∀ l∈P,l.bounded D) (hQ : ∀ l∈Q,l.bounded D) (i : ι) :
--       let B : NNReal := ⟨actualWordBound f R j A D,(actualWordBound_pos f hR hj hA hD).le⟩
--       let μ := Measure.pi (fun _ : MatrixCoordinates ι=>gaussianReal 0 1)
--       let s := truncationGoodSet r R lo hi (pathDiagonal a z) (pathShift z ((j/(Fintype.card ι:ℝ))*∑ k,a k))
--       |(∫ g,actualWord f R hR j a z (P++(.noise::Q)) (goeMatrix r g) i i ∂μ)-
--         r*(∫ g,actualWordLoop f hR j a z P Q (goeMatrix r g) i ∂μ)|≤
--         markedError (ι:=ι) r R ((P.length:NNReal)*B^P.length) ((Q.length:NNReal)*B^Q.length)
--           (B^P.length) (B^Q.length) (wordDifferentialBound B A z P.length)
--             (wordDifferentialBound B A z Q.length) (μ.real sᶜ)
--   ```
--
--   **Definitions.** The statement is written with `OAI.SKGap.MatrixCoordinates`, `OAI.SKGap.WordLetter`, `OAI.SKGap.actualWord`, `OAI.SKGap.actualWordBound`, `OAI.SKGap.actualWordBound_pos`, `OAI.SKGap.actualWordLoop`, `OAI.SKGap.goeMatrix`, `OAI.SKGap.markedError`, `OAI.SKGap.pathDiagonal`, `OAI.SKGap.pathShift`, `OAI.SKGap.truncationGoodSet`, `OAI.SKGap.wordDifferentialBound` and `OAI.SKGap.WordLetter.bounded` (definitions bundle `OAIQ072A000` of this split).
--
--   **Used by.** The proof of `OAI.SKGap.actual_word_simultaneous_prediction_of_cutoff` of this split imports it.
-- source:
--   OpenAI, A spectral gap throughout the high-temperature Sherrington-Kirkpatrick phase (result family 227), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 227; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/A-spectral-gap-throughout-the-high-temperature-Sherrington-Kirkpatrick-phase-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/SKGap/Matrix/WordLoop.lean (declaration OAI.SKGap.actualWord_loop)

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
open Matrix Real MeasureTheory ProbabilityTheory Set
open RealComplex
open scoped BigOperators Matrix.Norms.Frobenius NNReal ENNReal SchwartzMap
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem actualWord_loop [Nonempty ι] (f : 𝓢(ℝ,ℂ)) {lo hi : ℝ} (hlo : 0<lo)
    (hf : ∀ x∈Icc lo hi,f x=(x:ℂ)⁻¹) {R j A D z r : ℝ}
    (hR : 0≤R) (hj : 0≤j) (hA : 0≤A) (hD : 0≤D) (hr : 0 ≤ r) {a : ι→ℝ}
    (ha : ∀ i,0≤a i) (haA : ∀ i,a i≤A) (hz : z∈Icc (0:ℝ) 1)
    (P Q : List (WordLetter ι)) (hP : ∀ l∈P,l.bounded D) (hQ : ∀ l∈Q,l.bounded D) (i : ι) :
    let B : NNReal := ⟨actualWordBound f R j A D,(actualWordBound_pos f hR hj hA hD).le⟩
    let μ := Measure.pi (fun _ : MatrixCoordinates ι=>gaussianReal 0 1)
    let s := truncationGoodSet r R lo hi (pathDiagonal a z) (pathShift z ((j/(Fintype.card ι:ℝ))*∑ k,a k))
    |(∫ g,actualWord f R hR j a z (P++(.noise::Q)) (goeMatrix r g) i i ∂μ)-
      r*(∫ g,actualWordLoop f hR j a z P Q (goeMatrix r g) i ∂μ)|≤
      markedError (ι:=ι) r R ((P.length:NNReal)*B^P.length) ((Q.length:NNReal)*B^Q.length)
        (B^P.length) (B^Q.length) (wordDifferentialBound B A z P.length)
          (wordDifferentialBound B A z Q.length) (μ.real sᶜ) := by
  sorry
end SKGap
end
end

end OAI
end
