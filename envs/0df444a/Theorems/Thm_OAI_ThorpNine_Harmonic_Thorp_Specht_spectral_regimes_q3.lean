-- Prove2me | Theorems.Thm_OAI_ThorpNine_Harmonic_Thorp_Specht_spectral_regimes_q3
-- name    : OAI.ThorpNine.Harmonic.Thorp.Specht.spectral_regimes_q3
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T03:06:19.24498+00:00
-- url     : https://prove2.me/theorems/b0c7e7b0-a3c5-4a5d-a2f1-9ebc252209b1
-- title:
--   OAI.ThorpNine.Harmonic.Thorp.Specht.spectral_regimes_q3: intermediate lemma from OpenAI, Optimal-order mixing of the Thorp shuffle
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.ThorpResults.remaining_main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Optimal-order mixing of the Thorp shuffle*, OpenAI Math Release, September 26, 2026, result family 238, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ThorpNine.Harmonic.Thorp.Specht.spectral_regimes` of [lean/OAI/Probability/ThorpResults/ThorpRouting/Harmonic/TailShapes.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/ThorpResults/ThorpRouting/Harmonic/TailShapes.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ThorpNine.Harmonic.Thorp.Specht`, with `open scoped BigOperators Classical`, `open Filter UnitaryFinite DimensionEstimates`):
--
--   ```lean
--   theorem spectral_regimes_q3 :
--       ∃ a h : ℝ, 0<a ∧ 0<h ∧ ∀ᶠ d : ℕ in atTop,
--         ∀ (μ : YoungDiagram) (e : Card d ≃ Cell μ), 0<μ.card-μ.rowLen 0 →
--           (μ.colLen 0:ℝ)≤(μ.card:ℝ)/2 →
--           ‖sampleOperator (V := hilbertSpace μ) (relabelledUnitary μ e) (palindromePerm d)‖≤
--             Real.exp (-a*Real.log (Module.finrank ℂ (space μ))) ∧
--           1≤Real.log (Module.finrank ℂ (space μ)) ∧
--           (((1/2:ℝ)*Real.log μ.card≤Real.log (Module.finrank ℂ (space μ)) ∧
--             (μ.card-μ.rowLen 0:ℕ)≤Real.log (Module.finrank ℂ (space μ))) ∨
--             h*(2:ℝ)^d≤Real.log (Module.finrank ℂ (space μ)))
--   ```
--
--   **Definitions.** The statement is written with `OAI.ThorpNine.Harmonic.Thorp.BenesCoins`, `OAI.ThorpNine.Harmonic.Thorp.SwitchIndex`, `OAI.ThorpNine.Harmonic.Thorp.instDecidableEqSwitchIndex`, `OAI.ThorpNine.Harmonic.Thorp.instFintypeSwitchIndex` and `OAI.ThorpNine.Harmonic.Thorp.palindromePerm` (definitions bundle `OAIQ3Th000` of this split); `OAI.ThorpNine.Harmonic.Thorp.Card`, `OAI.ThorpNine.Harmonic.Thorp.PermutationHilbert.H`, `OAI.ThorpNine.Harmonic.Thorp.Specht.Cell`, `OAI.ThorpNine.Harmonic.Thorp.Specht.Tabloid`, `OAI.ThorpNine.Harmonic.Thorp.Specht.hilbertSpace`, `OAI.ThorpNine.Harmonic.Thorp.Specht.instFintypeTabloid`, `OAI.ThorpNine.Harmonic.Thorp.Specht.relabelledUnitary`, `OAI.ThorpNine.Harmonic.Thorp.Specht.rowIndex`, `OAI.ThorpNine.Harmonic.Thorp.Specht.space` and `OAI.ThorpNine.Harmonic.Thorp.UnitaryFinite.sampleOperator` (the published bundle `Def_ThorpRemaining`).
--
--   **Used by.** The proof of `OAI.ThorpResults.remaining_main` of this split imports it.
-- source:
--   OpenAI, Optimal-order mixing of the Thorp shuffle, OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 238; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Optimal-order-mixing-of-the-Thorp-shuffle-September-26-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/ThorpResults/ThorpRouting/Harmonic/TailShapes.lean (declaration OAI.ThorpNine.Harmonic.Thorp.Specht.spectral_regimes)

import Mathlib
import Definitions.Def_ThorpRemaining
import Definitions.Def_OAIQ3Th000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.Harmonic

namespace Thorp.Specht
open scoped BigOperators Classical
open Filter UnitaryFinite DimensionEstimates

theorem spectral_regimes_q3 :
    ∃ a h : ℝ, 0<a ∧ 0<h ∧ ∀ᶠ d : ℕ in atTop,
      ∀ (μ : YoungDiagram) (e : Card d ≃ Cell μ), 0<μ.card-μ.rowLen 0 →
        (μ.colLen 0:ℝ)≤(μ.card:ℝ)/2 →
        ‖sampleOperator (V := hilbertSpace μ) (relabelledUnitary μ e) (palindromePerm d)‖≤
          Real.exp (-a*Real.log (Module.finrank ℂ (space μ))) ∧
        1≤Real.log (Module.finrank ℂ (space μ)) ∧
        (((1/2:ℝ)*Real.log μ.card≤Real.log (Module.finrank ℂ (space μ)) ∧
          (μ.card-μ.rowLen 0:ℕ)≤Real.log (Module.finrank ℂ (space μ))) ∨
          h*(2:ℝ)^d≤Real.log (Module.finrank ℂ (space μ))) := by
  sorry

end Thorp.Specht

end ThorpNine.Harmonic

end OAI
end
