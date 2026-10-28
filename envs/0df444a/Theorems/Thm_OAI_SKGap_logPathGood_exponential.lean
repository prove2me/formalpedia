-- Prove2me | Theorems.Thm_OAI_SKGap_logPathGood_exponential
-- name    : OAI.SKGap.logPathGood_exponential
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T06:24:29.607027+00:00
-- url     : https://prove2.me/theorems/f349a2a9-e32c-4abc-828b-4f2695e44c67
-- title:
--   OAI.SKGap.logPathGood_exponential: intermediate lemma from OpenAI, A spectral gap throughout the high-temperature Sherrington-Kirkpatrick phase (result family 227)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SKGap.sk_main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A spectral gap throughout the high-temperature Sherrington-Kirkpatrick phase (result family 227)*, OpenAI Math Release, September 24, 2026, result family 227, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SKGap.logPathGood_exponential` of [lean/OAI/Probability/SKGap/Matrix/LogDetIntegral.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/SKGap/Matrix/LogDetIntegral.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SKGap`, with `open Matrix MeasureTheory ProbabilityTheory Real Set`, `open RealComplex`, `open scoped BigOperators Matrix.Norms.Frobenius SchwartzMap`):
--
--   ```lean
--   lemma logPathGood_exponential [Nonempty ι] {j A : ℝ} {a : ι → ℝ}
--       (hj : 0 < j) (hA : 0 < A) (ha : ∀ i, 0 ≤ a i) (haA : ∀ i, a i ≤ A)
--       (hs : sqrt j*A < 1)
--       (herr : 2*sqrt A*sqrt (sqrt (2*j^2*A^2/(Fintype.card ι:ℝ))) ≤ (1-sqrt j*A)^2/4) :
--       (Measure.pi (fun _ : MatrixCoordinates ι => gaussianReal 0 1)).real
--         {g | goeMatrix (j/(Fintype.card ι:ℝ)) g ∉
--           logPathGood (2*sqrt j+1+1) ((1-sqrt j*A)^2/4) (2+A*(2*sqrt j+1+j*A))
--             ((j/(Fintype.card ι:ℝ))*∑ b,a b) a} ≤ 3*Real.exp (-pathRate j A*(Fintype.card ι:ℝ))
--   ```
--
--   **Definitions.** The statement is written with `OAI.SKGap.MatrixCoordinates`, `OAI.SKGap.goeMatrix`, `OAI.SKGap.logPathGood` and `OAI.SKGap.pathRate` (definitions bundle `OAIQ072A000` of this split).
--
--   **Used by.** The proof of `OAI.SKGap.actual_logdet_mean` of this split imports it.
-- source:
--   OpenAI, A spectral gap throughout the high-temperature Sherrington-Kirkpatrick phase (result family 227), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 227; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/A-spectral-gap-throughout-the-high-temperature-Sherrington-Kirkpatrick-phase-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/SKGap/Matrix/LogDetIntegral.lean (declaration OAI.SKGap.logPathGood_exponential)

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
open Matrix MeasureTheory ProbabilityTheory Real Set
open RealComplex
open scoped BigOperators Matrix.Norms.Frobenius SchwartzMap
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma logPathGood_exponential [Nonempty ι] {j A : ℝ} {a : ι → ℝ}
    (hj : 0 < j) (hA : 0 < A) (ha : ∀ i, 0 ≤ a i) (haA : ∀ i, a i ≤ A)
    (hs : sqrt j*A < 1)
    (herr : 2*sqrt A*sqrt (sqrt (2*j^2*A^2/(Fintype.card ι:ℝ))) ≤ (1-sqrt j*A)^2/4) :
    (Measure.pi (fun _ : MatrixCoordinates ι => gaussianReal 0 1)).real
      {g | goeMatrix (j/(Fintype.card ι:ℝ)) g ∉
        logPathGood (2*sqrt j+1+1) ((1-sqrt j*A)^2/4) (2+A*(2*sqrt j+1+j*A))
          ((j/(Fintype.card ι:ℝ))*∑ b,a b) a} ≤ 3*Real.exp (-pathRate j A*(Fintype.card ι:ℝ)) := by
  sorry

end SKGap
end
end

end OAI
end
