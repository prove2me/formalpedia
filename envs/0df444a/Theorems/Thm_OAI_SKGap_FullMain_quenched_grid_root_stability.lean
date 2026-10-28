-- Prove2me | Theorems.Thm_OAI_SKGap_FullMain_quenched_grid_root_stability
-- name    : OAI.SKGap.FullMain.quenched_grid_root_stability
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T06:19:14.980681+00:00
-- url     : https://prove2.me/theorems/426b9b85-5c0f-4dce-bc8e-ea1421833748
-- title:
--   OAI.SKGap.FullMain.quenched_grid_root_stability: intermediate lemma from OpenAI, A spectral gap throughout the high-temperature Sherrington-Kirkpatrick phase (result family 227)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SKGap.sk_main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A spectral gap throughout the high-temperature Sherrington-Kirkpatrick phase (result family 227)*, OpenAI Math Release, September 24, 2026, result family 227, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SKGap.FullMain.quenched_grid_root_stability` of [lean/OAI/Probability/SKGap/Stability/RootGrid.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/SKGap/Stability/RootGrid.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SKGap.FullMain`, with `open MeasureTheory ProbabilityTheory Filter Real Set ObservationBridge GaussianHistory`, `open scoped Topology BigOperators ENNReal`):
--
--   ```lean
--   theorem quenched_grid_root_stability {β T : ℝ} (hβ : 0<β) (hβ1 : β<1) (hT : 0<T) :
--       ∃A K ε c ρ a : ℝ,1<A ∧ 2*β<K ∧ β*A<1 ∧ 0<ε ∧ 0 < c ∧ 0<ρ ∧ 0<a ∧
--         Whp β (fun n g=>operatorBound K (coupling g) ∧
--           gridFailure n (β^2) A K ε c ρ T g≤exp (-a*(n:ℝ)))
--   ```
--
--   **Definitions.** The statement is written with `OAI.SKGap.FullMain.Whp`, `OAI.SKGap.FullMain.gridFailure` and `OAI.SKGap.ObservationBridge.operatorBound` (definitions bundle `OAIQ072A000` of this split); `OAI.SKGap.Disorder` and `OAI.SKGap.coupling` (the published bundle `Def_SKHighTemperature`).
--
--   **Used by.** The proof of `OAI.SKGap.sk_main` of this split imports it.
-- source:
--   OpenAI, A spectral gap throughout the high-temperature Sherrington-Kirkpatrick phase (result family 227), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 227; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/A-spectral-gap-throughout-the-high-temperature-Sherrington-Kirkpatrick-phase-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/SKGap/Stability/RootGrid.lean (declaration OAI.SKGap.FullMain.quenched_grid_root_stability)

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
open MeasureTheory ProbabilityTheory Filter Real Set ObservationBridge GaussianHistory
open scoped Topology BigOperators ENNReal
noncomputable section

theorem quenched_grid_root_stability {β T : ℝ} (hβ : 0<β) (hβ1 : β<1) (hT : 0<T) :
    ∃A K ε c ρ a : ℝ,1<A ∧ 2*β<K ∧ β*A<1 ∧ 0<ε ∧ 0 < c ∧ 0<ρ ∧ 0<a ∧
      Whp β (fun n g=>operatorBound K (coupling g) ∧
        gridFailure n (β^2) A K ε c ρ T g≤exp (-a*(n:ℝ))) := by
  sorry

end
end SKGap.FullMain

end OAI
end
