-- Prove2me | Theorems.Thm_OAI_SKGap_generalTemplateGaussian_centered_continuous_s2
-- name    : OAI.SKGap.generalTemplateGaussian_centered_continuous_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T10:47:45.956434+00:00
-- url     : https://prove2.me/theorems/b7192914-b009-4878-9a2d-a19dd25e2c1a
-- title:
--   OAI.SKGap.generalTemplateGaussian_centered_continuous_s2: intermediate lemma from OpenAI, Critical mixing in the Sherrington-Kirkpatrick model (result family 227)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CriticalSK.critical_mixing_bounds`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Critical mixing in the Sherrington-Kirkpatrick model (result family 227)*, OpenAI Math Release, September 25, 2026, result family 227, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SKGap`, with `open Matrix Real Set MeasureTheory ProbabilityTheory Filter`, `open scoped BigOperators Matrix.Norms.Frobenius SchwartzMap Topology`):
--
--   ```lean
--   lemma generalTemplateGaussian_centered_continuous_s2 [Nonempty ι] (f : 𝓢(ℝ,ℂ)) {R j A D : ℝ}
--       (hR : 0 ≤ R) (hj : 0 ≤ j) (hA : 0 ≤ A) (hD : 0 ≤ D) (F : List (WordTemplateLetter m)) (r : ℝ)
--       (g : EuclideanSpace ℝ (MatrixCoordinates ι)) :
--       Continuous (fun θ : WordParameter m ι=>matrixCentered
--         (fun x : EuclideanSpace ℝ (MatrixCoordinates ι)=>generalTemplateMatrix f R hR j A D F θ (goeMatrix r x)) g)
--   ```
--
--   **Definitions.** The statement is written with `OAI.SKGap.MatrixCoordinates`, `OAI.SKGap.WordParameter`, `OAI.SKGap.WordTemplateLetter`, `OAI.SKGap.generalTemplateMatrix`, `OAI.SKGap.goeMatrix` and `OAI.SKGap.matrixCentered` (definitions bundle `OAIQ072A000` of this split).
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
open Matrix Real Set MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Matrix.Norms.Frobenius SchwartzMap Topology
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ}

lemma generalTemplateGaussian_centered_continuous_s2 [Nonempty ι] (f : 𝓢(ℝ,ℂ)) {R j A D : ℝ}
    (hR : 0 ≤ R) (hj : 0 ≤ j) (hA : 0 ≤ A) (hD : 0 ≤ D) (F : List (WordTemplateLetter m)) (r : ℝ)
    (g : EuclideanSpace ℝ (MatrixCoordinates ι)) :
    Continuous (fun θ : WordParameter m ι=>matrixCentered
      (fun x : EuclideanSpace ℝ (MatrixCoordinates ι)=>generalTemplateMatrix f R hR j A D F θ (goeMatrix r x)) g) := by
  sorry
end SKGap
end
end

end OAI
end
