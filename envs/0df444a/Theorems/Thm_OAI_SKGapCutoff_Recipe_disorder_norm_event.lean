-- Prove2me | Theorems.Thm_OAI_SKGapCutoff_Recipe_disorder_norm_event
-- name    : OAI.SKGapCutoff.Recipe.disorder_norm_event
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T06:25:27.573345+00:00
-- url     : https://prove2.me/theorems/dc2c6e8e-7c3d-4954-90f5-37e26888b3e0
-- title:
--   OAI.SKGapCutoff.Recipe.disorder_norm_event: intermediate lemma from OpenAI, A spectral gap throughout the high-temperature Sherrington-Kirkpatrick phase (result family 227)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SKGap.sk_main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A spectral gap throughout the high-temperature Sherrington-Kirkpatrick phase (result family 227)*, OpenAI Math Release, September 24, 2026, result family 227, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SKGapCutoff.Recipe.disorder_norm_event` of [lean/OAI/Probability/SKGap/Localization/DisorderRecipeEvent.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/SKGap/Localization/DisorderRecipeEvent.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SKGapCutoff.Recipe`, with `open scoped BigOperators Matrix.Norms.Frobenius`, `open scoped BigOperators Topology`, `open SKGap SKGap.ObservationBridge SKGap.Noncrossing SKGap.Noncrossing.Primary`, `open MeasureTheory ProbabilityTheory Real Set Filter`):
--
--   ```lean
--   lemma disorder_norm_event {β : ℝ} (hβ : 0<β) {n : ℕ} (hn : 0<n) :
--       SKGap.disorderLaw β n {g | physicalNormBound (β^2)<SKGap.opNorm (coupling g)}≤
--         recipeNormTail (β^2) n
--   ```
--
--   **Definitions.** The statement is written with `OAI.SKGap.opNorm` (definitions bundle `OAIQ072A000` of this split); `OAI.SKGapCutoff.Recipe.physicalNormBound` and `OAI.SKGapCutoff.Recipe.recipeNormTail` (definitions bundle `OAIQ072A001` of this split); `OAI.SKGap.Disorder`, `OAI.SKGap.Edge`, `OAI.SKGap.coupling` and `OAI.SKGap.disorderLaw` (the published bundle `Def_SKHighTemperature`).
--
--   **Used by.** The proofs of `OAI.SKGap.FullMain.quenched_posterior_covariance` and `OAI.SKGap.sk_main` of this split import it.
-- source:
--   OpenAI, A spectral gap throughout the high-temperature Sherrington-Kirkpatrick phase (result family 227), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 227; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/A-spectral-gap-throughout-the-high-temperature-Sherrington-Kirkpatrick-phase-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/SKGap/Localization/DisorderRecipeEvent.lean (declaration OAI.SKGapCutoff.Recipe.disorder_norm_event)

import Mathlib
import Definitions.Def_SKHighTemperature
import Definitions.Def_OAIQ072A000
import Definitions.Def_OAIQ072A001

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius

noncomputable section
open scoped BigOperators Topology
namespace SKGapCutoff.Recipe
open SKGap SKGap.ObservationBridge SKGap.Noncrossing SKGap.Noncrossing.Primary
open MeasureTheory ProbabilityTheory Real Set Filter

lemma disorder_norm_event {β : ℝ} (hβ : 0<β) {n : ℕ} (hn : 0<n) :
    SKGap.disorderLaw β n {g | physicalNormBound (β^2)<SKGap.opNorm (coupling g)}≤
      recipeNormTail (β^2) n := by
  sorry

end SKGapCutoff.Recipe

end
end
end

end OAI
end
