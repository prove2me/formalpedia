-- Prove2me | Theorems.Thm_OAI_SKGap_actualWord_expected_recursion_s2
-- name    : OAI.SKGap.actualWord_expected_recursion_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T10:47:38.723178+00:00
-- url     : https://prove2.me/theorems/8b9ea29b-6d71-43ea-94e7-d34ac5e6d51c
-- title:
--   OAI.SKGap.actualWord_expected_recursion_s2: intermediate lemma from OpenAI, Critical mixing in the Sherrington-Kirkpatrick model (result family 227)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CriticalSK.critical_mixing_bounds`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Critical mixing in the Sherrington-Kirkpatrick model (result family 227)*, OpenAI Math Release, September 25, 2026, result family 227, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SKGap`, with `open Matrix Real MeasureTheory ProbabilityTheory Set`, `open scoped BigOperators Matrix.Norms.Frobenius SchwartzMap`):
--
--   ```lean
--   theorem actualWord_expected_recursion_s2 {n : ℕ} (hn : 0<n) (f : 𝓢(ℝ,ℂ))
--       {j A D z : ℝ} (hj : 0<j) (hA : 0<A) (hD : 0≤D) (hs : sqrt j*A<1)
--       (hf : ∀ x∈Icc ((1-sqrt j*A)^2/4) (2+A*(2*sqrt j+1+j*A)),f x=(x:ℂ)⁻¹)
--       (herr : 2*sqrt A*sqrt (sqrt (2*j^2*A^2/(n:ℝ)))≤(1-sqrt j*A)^2/4)
--       {a : Fin n→ℝ} (ha : ∀ i,0≤a i) (haA : ∀ i,a i≤A) (haD : ∀ i,|a i|≤D)
--       (hz : z∈Icc (0:ℝ) 1) (P Q : List (WordLetter (Fin n)))
--       (hP : ∀ l∈P,l.bounded D) (hQ : ∀ l∈Q,l.bounded D) (i : Fin n) :
--       let R := 2*sqrt j+1+1
--       let hR : 0≤R := by dsimp [R];positivity
--       let B : NNReal := ⟨actualWordBound f R j A D,(actualWordBound_pos f hR hj.le hA.le hD).le⟩
--       |wordExpected f hR j a z (P++(.noise::Q)) i-wordRecursionAtExpected f hR j a z P Q i|≤
--         (wordMarkedCost B j R A (pathRate j A) z P.length Q.length+
--           wordRecursionAtCost j B z a P Q)/(n:ℝ)
--   ```
--
--   **Definitions.** The statement is written with `OAI.SKGap.WordLetter`, `OAI.SKGap.actualWordBound`, `OAI.SKGap.actualWordBound_pos`, `OAI.SKGap.pathRate`, `OAI.SKGap.wordExpected`, `OAI.SKGap.wordMarkedCost`, `OAI.SKGap.wordRecursionAtCost`, `OAI.SKGap.wordRecursionAtExpected` and `OAI.SKGap.WordLetter.bounded` (definitions bundle `OAIQ072A000` of this split).
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
open Matrix Real MeasureTheory ProbabilityTheory Set
open scoped BigOperators Matrix.Norms.Frobenius SchwartzMap

theorem actualWord_expected_recursion_s2 {n : ℕ} (hn : 0<n) (f : 𝓢(ℝ,ℂ))
    {j A D z : ℝ} (hj : 0<j) (hA : 0<A) (hD : 0≤D) (hs : sqrt j*A<1)
    (hf : ∀ x∈Icc ((1-sqrt j*A)^2/4) (2+A*(2*sqrt j+1+j*A)),f x=(x:ℂ)⁻¹)
    (herr : 2*sqrt A*sqrt (sqrt (2*j^2*A^2/(n:ℝ)))≤(1-sqrt j*A)^2/4)
    {a : Fin n→ℝ} (ha : ∀ i,0≤a i) (haA : ∀ i,a i≤A) (haD : ∀ i,|a i|≤D)
    (hz : z∈Icc (0:ℝ) 1) (P Q : List (WordLetter (Fin n)))
    (hP : ∀ l∈P,l.bounded D) (hQ : ∀ l∈Q,l.bounded D) (i : Fin n) :
    let R := 2*sqrt j+1+1
    let hR : 0≤R := by dsimp [R];positivity
    let B : NNReal := ⟨actualWordBound f R j A D,(actualWordBound_pos f hR hj.le hA.le hD).le⟩
    |wordExpected f hR j a z (P++(.noise::Q)) i-wordRecursionAtExpected f hR j a z P Q i|≤
      (wordMarkedCost B j R A (pathRate j A) z P.length Q.length+
        wordRecursionAtCost j B z a P Q)/(n:ℝ) := by
  sorry
end SKGap
end
end

end OAI
end
