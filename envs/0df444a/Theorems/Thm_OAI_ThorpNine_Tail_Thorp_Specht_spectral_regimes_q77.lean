-- Prove2me | Theorems.Thm_OAI_ThorpNine_Tail_Thorp_Specht_spectral_regimes_q77
-- name    : OAI.ThorpNine.Tail.Thorp.Specht.spectral_regimes_q77
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T09:58:01.110081+00:00
-- url     : https://prove2.me/theorems/41fba431-9548-43e8-aee1-5e166518e399
-- title:
--   OAI.ThorpNine.Tail.Thorp.Specht.spectral_regimes_q77: intermediate lemma from OpenAI, Optimal logarithmic mixing of the Thorp shuffle (routing densities)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.ThorpNine.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Optimal logarithmic mixing of the Thorp shuffle (routing densities)*, OpenAI Math Release, September 26, 2026, result family 238, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ThorpNine.Tail.Thorp.Specht.spectral_regimes` of [lean/OAI/Probability/ThorpRouting/Tail/TailShapes.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/ThorpRouting/Tail/TailShapes.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ThorpNine.Tail.Thorp.Specht`, with `open scoped BigOperators Classical`, `open Filter UnitaryFinite DimensionEstimates`):
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
--   **Definitions.** The statement is written with `OAI.ThorpNine.Tail.Thorp.BenesCoins` and `OAI.ThorpNine.Tail.Thorp.palindromePerm` (definitions bundle `OAIQ077T002` of this split); `OAI.ThorpNine.Tail.Thorp.Card`, `OAI.ThorpNine.Tail.Thorp.SwitchIndex`, `OAI.ThorpNine.Tail.Thorp.instDecidableEqSwitchIndex`, `OAI.ThorpNine.Tail.Thorp.instFintypeSwitchIndex`, `OAI.ThorpNine.Tail.Thorp.PermutationHilbert.H`, `OAI.ThorpNine.Tail.Thorp.Specht.Cell`, `OAI.ThorpNine.Tail.Thorp.Specht.Tabloid`, `OAI.ThorpNine.Tail.Thorp.Specht.hilbertSpace`, `OAI.ThorpNine.Tail.Thorp.Specht.instFintypeTabloid`, `OAI.ThorpNine.Tail.Thorp.Specht.relabelledUnitary`, `OAI.ThorpNine.Tail.Thorp.Specht.rowIndex`, `OAI.ThorpNine.Tail.Thorp.Specht.space` and `OAI.ThorpNine.Tail.Thorp.UnitaryFinite.sampleOperator` (the published bundle `Def_ThorpRouting`).
--
--   **Used by.** The proof of `OAI.ThorpNine.Tail.Thorp.StrongTail.strong_tail_q77` of this split imports it.
-- source:
--   OpenAI, Optimal logarithmic mixing of the Thorp shuffle (routing densities), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 238; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Routing-densities-and-representation-contraction-for-Thorp-sweeps-September-26-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/ThorpRouting/Tail/TailShapes.lean (declaration OAI.ThorpNine.Tail.Thorp.Specht.spectral_regimes)

import Mathlib
import Definitions.Def_ThorpRouting
import Definitions.Def_OAIQ077T002

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.Tail

namespace Thorp.Specht
open scoped BigOperators Classical
open Filter UnitaryFinite DimensionEstimates

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

end ThorpNine.Tail

end OAI
end
