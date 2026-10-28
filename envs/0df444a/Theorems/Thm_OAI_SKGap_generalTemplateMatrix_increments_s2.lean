-- Prove2me | Theorems.Thm_OAI_SKGap_generalTemplateMatrix_increments_s2
-- name    : OAI.SKGap.generalTemplateMatrix_increments_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T10:48:09.7774+00:00
-- url     : https://prove2.me/theorems/c1169aa9-f1a7-420f-bb41-3f4661ef90d9
-- title:
--   OAI.SKGap.generalTemplateMatrix_increments_s2: intermediate lemma from OpenAI, Critical mixing in the Sherrington-Kirkpatrick model (result family 227)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CriticalSK.critical_mixing_bounds`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Critical mixing in the Sherrington-Kirkpatrick model (result family 227)*, OpenAI Math Release, September 25, 2026, result family 227, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SKGap`, with `open Matrix Real Set`, `open scoped BigOperators Matrix.Norms.Frobenius SchwartzMap`):
--
--   ```lean
--   theorem generalTemplateMatrix_increments_s2 [Nonempty ι] (f : 𝓢(ℝ,ℂ)) {R j A D : ℝ}
--       (hR : 0 ≤ R) (hj : 0 ≤ j) (hA : 0 ≤ A) (hD : 0 ≤ D)
--       (F : List (WordTemplateLetter m)) (θ η : WordParameter m ι) :
--       let B : NNReal := ⟨actualWordBound f R j A D,(actualWordBound_pos f hR hj hA hD).le⟩
--       let Δ : NNReal := ⟨generalTemplateHolder f R j A D*sqrt (dist θ η),mul_nonneg (generalTemplateHolder_nonneg f hR hj hA hD) (sqrt_nonneg _)⟩
--       (∀ M,opNorm (generalTemplateMatrix f R hR j A D F θ M-generalTemplateMatrix f R hR j A D F η M) ≤
--         (wordParameterCoeff B F.length:ℝ)*Δ) ∧
--       LipschitzWith (wordMixedCoeff B F.length*Δ)
--         (fun M=>generalTemplateMatrix f R hR j A D F θ M-generalTemplateMatrix f R hR j A D F η M)
--   ```
--
--   **Definitions.** The statement is written with `OAI.SKGap.WordParameter`, `OAI.SKGap.WordTemplateLetter`, `OAI.SKGap.actualWordBound`, `OAI.SKGap.actualWordBound_pos`, `OAI.SKGap.generalTemplateHolder`, `OAI.SKGap.generalTemplateHolder_nonneg`, `OAI.SKGap.generalTemplateMatrix`, `OAI.SKGap.opNorm`, `OAI.SKGap.wordMixedCoeff` and `OAI.SKGap.wordParameterCoeff` (definitions bundle `OAIQ072A000` of this split).
--
--   **Used by.** The proof of `OAI.SKGap.generalTemplateGaussian_centered_continuous_s2` of this split imports it.
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
open Matrix Real Set
open scoped BigOperators Matrix.Norms.Frobenius SchwartzMap
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ}

theorem generalTemplateMatrix_increments_s2 [Nonempty ι] (f : 𝓢(ℝ,ℂ)) {R j A D : ℝ}
    (hR : 0 ≤ R) (hj : 0 ≤ j) (hA : 0 ≤ A) (hD : 0 ≤ D)
    (F : List (WordTemplateLetter m)) (θ η : WordParameter m ι) :
    let B : NNReal := ⟨actualWordBound f R j A D,(actualWordBound_pos f hR hj hA hD).le⟩
    let Δ : NNReal := ⟨generalTemplateHolder f R j A D*sqrt (dist θ η),mul_nonneg (generalTemplateHolder_nonneg f hR hj hA hD) (sqrt_nonneg _)⟩
    (∀ M,opNorm (generalTemplateMatrix f R hR j A D F θ M-generalTemplateMatrix f R hR j A D F η M) ≤
      (wordParameterCoeff B F.length:ℝ)*Δ) ∧
    LipschitzWith (wordMixedCoeff B F.length*Δ)
      (fun M=>generalTemplateMatrix f R hR j A D F θ M-generalTemplateMatrix f R hR j A D F η M) := by
  sorry
end SKGap
end
end

end OAI
end
