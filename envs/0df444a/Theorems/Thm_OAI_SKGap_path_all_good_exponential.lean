-- Prove2me | Theorems.Thm_OAI_SKGap_path_all_good_exponential
-- name    : OAI.SKGap.path_all_good_exponential
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T06:22:57.537225+00:00
-- url     : https://prove2.me/theorems/7cef8458-1b75-405f-a7c2-9b5513a8a6ae
-- title:
--   OAI.SKGap.path_all_good_exponential: intermediate lemma from OpenAI, A spectral gap throughout the high-temperature Sherrington-Kirkpatrick phase (result family 227)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SKGap.sk_main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A spectral gap throughout the high-temperature Sherrington-Kirkpatrick phase (result family 227)*, OpenAI Math Release, September 24, 2026, result family 227, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SKGap.path_all_good_exponential` of [lean/OAI/Probability/SKGap/Localization/Bilinear2.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/SKGap/Localization/Bilinear2.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SKGap`, with `open Matrix MeasureTheory ProbabilityTheory Real Set Filter`, `open RealComplex`, `open scoped BigOperators Matrix.Norms.Frobenius NNReal ENNReal SchwartzMap Topology`):
--
--   ```lean
--   lemma path_all_good_exponential [Nonempty ι] {j A : ℝ} {a : ι → ℝ}
--       (hj : 0 < j) (hA0 : 0 < A) (ha : ∀ i, 0 ≤ a i) (haA : ∀ i, a i ≤ A)
--       (hs : sqrt j*A < 1)
--       (herr : 2*sqrt A*sqrt (sqrt (2*j^2*A^2/(Fintype.card ι:ℝ))) ≤ (1-sqrt j*A)^2/4) :
--       (Measure.pi (fun _ : MatrixCoordinates ι => gaussianReal 0 1)).real
--         {g | ∃ z ∈ Icc (0:ℝ) 1, g ∉ truncationGoodSet (j/(Fintype.card ι:ℝ))
--           (2*sqrt j+1+1) ((1-sqrt j*A)^2/4) (2+A*(2*sqrt j+1+j*A))
--           (pathDiagonal a z) (pathShift z ((j/(Fintype.card ι:ℝ))*∑ b,a b))} ≤
--         3*exp (-pathRate j A*(Fintype.card ι:ℝ))
--   ```
--
--   **Definitions.** The statement is written with `OAI.SKGap.MatrixCoordinates`, `OAI.SKGap.pathDiagonal`, `OAI.SKGap.pathRate`, `OAI.SKGap.pathShift` and `OAI.SKGap.truncationGoodSet` (definitions bundle `OAIQ072A000` of this split).
--
--   **Used by.** The proofs of `OAI.SKGap.compact_conditional_uniform_tail` and `OAI.SKGap.logPathGood_exponential` of this split import it.
-- source:
--   OpenAI, A spectral gap throughout the high-temperature Sherrington-Kirkpatrick phase (result family 227), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 227; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/A-spectral-gap-throughout-the-high-temperature-Sherrington-Kirkpatrick-phase-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/SKGap/Localization/Bilinear2.lean (declaration OAI.SKGap.path_all_good_exponential)

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
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma path_all_good_exponential [Nonempty ι] {j A : ℝ} {a : ι → ℝ}
    (hj : 0 < j) (hA0 : 0 < A) (ha : ∀ i, 0 ≤ a i) (haA : ∀ i, a i ≤ A)
    (hs : sqrt j*A < 1)
    (herr : 2*sqrt A*sqrt (sqrt (2*j^2*A^2/(Fintype.card ι:ℝ))) ≤ (1-sqrt j*A)^2/4) :
    (Measure.pi (fun _ : MatrixCoordinates ι => gaussianReal 0 1)).real
      {g | ∃ z ∈ Icc (0:ℝ) 1, g ∉ truncationGoodSet (j/(Fintype.card ι:ℝ))
        (2*sqrt j+1+1) ((1-sqrt j*A)^2/4) (2+A*(2*sqrt j+1+j*A))
        (pathDiagonal a z) (pathShift z ((j/(Fintype.card ι:ℝ))*∑ b,a b))} ≤
      3*exp (-pathRate j A*(Fintype.card ι:ℝ)) := by
  sorry
end SKGap
end
end

end OAI
end
