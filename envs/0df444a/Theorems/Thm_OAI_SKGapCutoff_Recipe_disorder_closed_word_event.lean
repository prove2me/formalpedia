-- Prove2me | Theorems.Thm_OAI_SKGapCutoff_Recipe_disorder_closed_word_event
-- name    : OAI.SKGapCutoff.Recipe.disorder_closed_word_event
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T06:27:35.530985+00:00
-- url     : https://prove2.me/theorems/28b2e947-78b6-4dd0-91e7-6c316571931f
-- title:
--   OAI.SKGapCutoff.Recipe.disorder_closed_word_event: intermediate lemma from OpenAI, A spectral gap throughout the high-temperature Sherrington-Kirkpatrick phase (result family 227)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SKGap.sk_main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A spectral gap throughout the high-temperature Sherrington-Kirkpatrick phase (result family 227)*, OpenAI Math Release, September 24, 2026, result family 227, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SKGapCutoff.Recipe.disorder_closed_word_event` of [lean/OAI/Probability/SKGap/Matrix/BufferedClosedWord.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/SKGap/Matrix/BufferedClosedWord.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SKGapCutoff.Recipe`, with `open scoped BigOperators Topology Matrix.Norms.Frobenius`, `open SKGap SKGap.Noncrossing SKGap.Noncrossing.Primary Matrix MeasureTheory ProbabilityTheory Real Set Filter`):
--
--   ```lean
--   theorem disorder_closed_word_event {β A D c : ℝ} (hβ : 0<β) (hA : 0<A)
--       (hs : sqrt (β^2)*A<1) (hD : 1≤D) (hAD : A≤D) (hc : 0 < c) (L : ℕ) :
--       ∃C:ℝ,∃N:ℕ,0<C ∧ 0<N ∧ ∀n,N≤n→
--         SKGap.disorderLaw β n {g | ¬ClosedWordEvent (β^2) A D c C L (coupling g)}≤
--           ordinaryWordTail (β^2) L n
--   ```
--
--   **Definitions.** The statement is written with `OAI.SKGapCutoff.Recipe.ClosedWordEvent` (definitions bundle `OAIQ072A000` of this split); `OAI.SKGapCutoff.Recipe.ordinaryWordTail` (definitions bundle `OAIQ072A002` of this split); `OAI.SKGap.Disorder`, `OAI.SKGap.Edge`, `OAI.SKGap.coupling` and `OAI.SKGap.disorderLaw` (the published bundle `Def_SKHighTemperature`).
--
--   **Used by.** The proof of `OAI.SKGap.FullMain.quenched_posterior_covariance` of this split imports it.
-- source:
--   OpenAI, A spectral gap throughout the high-temperature Sherrington-Kirkpatrick phase (result family 227), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 227; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/A-spectral-gap-throughout-the-high-temperature-Sherrington-Kirkpatrick-phase-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/SKGap/Matrix/BufferedClosedWord.lean (declaration OAI.SKGapCutoff.Recipe.disorder_closed_word_event)

import Mathlib
import Definitions.Def_SKHighTemperature
import Definitions.Def_OAIQ072A002

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Topology Matrix.Norms.Frobenius
namespace SKGapCutoff.Recipe
open SKGap SKGap.Noncrossing SKGap.Noncrossing.Primary Matrix MeasureTheory ProbabilityTheory Real Set Filter
variable {n : ℕ}

theorem disorder_closed_word_event {β A D c : ℝ} (hβ : 0<β) (hA : 0<A)
    (hs : sqrt (β^2)*A<1) (hD : 1≤D) (hAD : A≤D) (hc : 0 < c) (L : ℕ) :
    ∃C:ℝ,∃N:ℕ,0<C ∧ 0<N ∧ ∀n,N≤n→
      SKGap.disorderLaw β n {g | ¬ClosedWordEvent (β^2) A D c C L (coupling g)}≤
        ordinaryWordTail (β^2) L n := by
  sorry

end SKGapCutoff.Recipe

end
end

end OAI
end
