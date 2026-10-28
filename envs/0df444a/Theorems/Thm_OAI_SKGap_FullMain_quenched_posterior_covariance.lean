-- Prove2me | Theorems.Thm_OAI_SKGap_FullMain_quenched_posterior_covariance
-- name    : OAI.SKGap.FullMain.quenched_posterior_covariance
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T06:18:50.636478+00:00
-- url     : https://prove2.me/theorems/80686fec-de60-4ac0-bbe1-31a3f87645a4
-- title:
--   OAI.SKGap.FullMain.quenched_posterior_covariance: intermediate lemma from OpenAI, A spectral gap throughout the high-temperature Sherrington-Kirkpatrick phase (result family 227)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SKGap.sk_main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A spectral gap throughout the high-temperature Sherrington-Kirkpatrick phase (result family 227)*, OpenAI Math Release, September 24, 2026, result family 227, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SKGap.FullMain.quenched_posterior_covariance` of [lean/OAI/Probability/SKGap/Posterior/QuenchedPosterior.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/SKGap/Posterior/QuenchedPosterior.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SKGap.FullMain`, with `open MeasureTheory ProbabilityTheory Filter Set Real`, `open scoped Topology BigOperators`, `open SKGapCutoff SKGapCutoff.Recipe SKGapCutoff.Primary SKGapCutoff.Static`):
--
--   ```lean
--   theorem quenched_posterior_covariance {β Aroot ε c r₀ : ℝ}
--       (hβ : 0<β) (hβ1 : β<1) (hAroot : 1<Aroot) (hs : β*Aroot<1)
--       (hε : 0<ε) (hc : 0 < c) (hr₀ : 0 < r₀) :
--       ∃D : ℝ,0≤D ∧ Whp β (fun n g=>PosteriorCovarianceProperty (n := n) (β^2) Aroot ε c r₀ D g)
--   ```
--
--   **Definitions.** The statement is written with `OAI.SKGap.FullMain.PosteriorCovarianceProperty` and `OAI.SKGap.FullMain.Whp` (definitions bundle `OAIQ072A000` of this split); `OAI.SKGap.Disorder` (the published bundle `Def_SKHighTemperature`).
--
--   **Used by.** The proof of `OAI.SKGap.sk_main` of this split imports it.
-- source:
--   OpenAI, A spectral gap throughout the high-temperature Sherrington-Kirkpatrick phase (result family 227), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 227; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/A-spectral-gap-throughout-the-high-temperature-Sherrington-Kirkpatrick-phase-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/SKGap/Posterior/QuenchedPosterior.lean (declaration OAI.SKGap.FullMain.quenched_posterior_covariance)

import Mathlib
import Definitions.Def_SKHighTemperature
import Definitions.Def_OAIQ072A000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SKGap.FullMain
open MeasureTheory ProbabilityTheory Filter Set Real
open scoped Topology BigOperators
open SKGapCutoff SKGapCutoff.Recipe SKGapCutoff.Primary SKGapCutoff.Static
noncomputable section

theorem quenched_posterior_covariance {β Aroot ε c r₀ : ℝ}
    (hβ : 0<β) (hβ1 : β<1) (hAroot : 1<Aroot) (hs : β*Aroot<1)
    (hε : 0<ε) (hc : 0 < c) (hr₀ : 0 < r₀) :
    ∃D : ℝ,0≤D ∧ Whp β (fun n g=>PosteriorCovarianceProperty (n := n) (β^2) Aroot ε c r₀ D g) := by
  sorry

end
end SKGap.FullMain

end OAI
end
