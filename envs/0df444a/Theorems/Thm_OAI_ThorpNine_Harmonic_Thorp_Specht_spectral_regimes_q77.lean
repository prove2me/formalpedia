-- Prove2me | Theorems.Thm_OAI_ThorpNine_Harmonic_Thorp_Specht_spectral_regimes_q77
-- name    : OAI.ThorpNine.Harmonic.Thorp.Specht.spectral_regimes_q77
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T09:52:58.035588+00:00
-- url     : https://prove2.me/theorems/e65482e9-97d9-4232-be4c-adc2e8149af9
-- title:
--   OAI.ThorpNine.Harmonic.Thorp.Specht.spectral_regimes_q77: intermediate lemma from OpenAI, Optimal logarithmic mixing of the Thorp shuffle (routing densities)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.ThorpNine.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Optimal logarithmic mixing of the Thorp shuffle (routing densities)*, OpenAI Math Release, September 26, 2026, result family 238, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ThorpNine.Harmonic.Thorp.Specht.spectral_regimes` of [lean/OAI/Probability/ThorpRouting/Harmonic/TailShapes.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/ThorpRouting/Harmonic/TailShapes.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ThorpNine.Harmonic.Thorp.Specht`, with `open scoped BigOperators Classical`, `open Filter UnitaryFinite`):
--
--   ```lean
--   theorem spectral_regimes_q77 :
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
--   **Definitions.** The statement is written with `OAI.ThorpNine.Harmonic.Thorp.BenesCoins`, `OAI.ThorpNine.Harmonic.Thorp.Card`, `OAI.ThorpNine.Harmonic.Thorp.SwitchIndex`, `OAI.ThorpNine.Harmonic.Thorp.instDecidableEqSwitchIndex`, `OAI.ThorpNine.Harmonic.Thorp.instFintypeSwitchIndex`, `OAI.ThorpNine.Harmonic.Thorp.palindromePerm`, `OAI.ThorpNine.Harmonic.Thorp.PermutationHilbert.H`, `OAI.ThorpNine.Harmonic.Thorp.Specht.Cell`, `OAI.ThorpNine.Harmonic.Thorp.Specht.Tabloid`, `OAI.ThorpNine.Harmonic.Thorp.Specht.hilbertSpace`, `OAI.ThorpNine.Harmonic.Thorp.Specht.instFintypeTabloid`, `OAI.ThorpNine.Harmonic.Thorp.Specht.relabelledUnitary`, `OAI.ThorpNine.Harmonic.Thorp.Specht.rowIndex`, `OAI.ThorpNine.Harmonic.Thorp.Specht.space` and `OAI.ThorpNine.Harmonic.Thorp.UnitaryFinite.sampleOperator` (the published bundle `Def_ThorpRouting`).
--
--   **Used by.** The proofs of `OAI.ThorpNine.Harmonic.Thorp.Casimir.eventual_level_contraction_q77` and `OAI.ThorpNine.Harmonic.Thorp.HarmonicBounds.dimension_contraction_q77` of this split import it.
-- source:
--   OpenAI, Optimal logarithmic mixing of the Thorp shuffle (routing densities), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 238; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Routing-densities-and-representation-contraction-for-Thorp-sweeps-September-26-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/ThorpRouting/Harmonic/TailShapes.lean (declaration OAI.ThorpNine.Harmonic.Thorp.Specht.spectral_regimes)

import Mathlib
import Definitions.Def_ThorpRouting

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.Harmonic

namespace Thorp.Specht
open scoped BigOperators Classical
open Filter UnitaryFinite

theorem spectral_regimes_q77 :
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
