-- Prove2me | Theorems.Thm_OAI_ThorpNine_Casimir_Thorp_CasimirBounds_trace_bound_q77
-- name    : OAI.ThorpNine.Casimir.Thorp.CasimirBounds.trace_bound_q77
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T09:56:22.513983+00:00
-- url     : https://prove2.me/theorems/13be2f7c-e90f-4b04-bee7-68a96256879b
-- title:
--   OAI.ThorpNine.Casimir.Thorp.CasimirBounds.trace_bound_q77: intermediate lemma from OpenAI, Optimal logarithmic mixing of the Thorp shuffle (routing densities)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.ThorpNine.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Optimal logarithmic mixing of the Thorp shuffle (routing densities)*, OpenAI Math Release, September 26, 2026, result family 238, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ThorpNine.Casimir.Thorp.CasimirBounds.trace_bound` of [lean/OAI/Probability/ThorpRouting/Casimir/Main.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/ThorpRouting/Casimir/Main.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ThorpNine.Casimir.Thorp.CasimirBounds`, with `open scoped BigOperators Classical`, `open UnitaryFinite`):
--
--   ```lean
--   lemma trace_bound_q77 (d : ℕ) (μ : YoungDiagram) (e : Card d ≃ Specht.Cell μ) :
--       (Module.finrank ℂ (Specht.space μ):ℝ)*traceMoment d μ e 65 ≤
--         Real.exp ((1+64*(1+heightDecay 1))*levelScale (2^d) (μ.card-μ.rowLen 0))
--   ```
--
--   **Definitions.** The statement is written with `OAI.ThorpNine.Casimir.Thorp.heightDecay` (definitions bundle `OAIQ077T001` of this split); `OAI.ThorpNine.Casimir.Thorp.Card`, `OAI.ThorpNine.Casimir.Thorp.CasimirBounds.levelScale`, `OAI.ThorpNine.Casimir.Thorp.CasimirBounds.traceMoment`, `OAI.ThorpNine.Casimir.Thorp.Specht.Cell`, `OAI.ThorpNine.Casimir.Thorp.Specht.Tabloid` and `OAI.ThorpNine.Casimir.Thorp.Specht.space` (the published bundle `Def_ThorpRouting`).
--
--   **Used by.** The proof of `OAI.ThorpNine.Casimir.Thorp.CasimirBounds.casimir_main_q77` of this split imports it.
-- source:
--   OpenAI, Optimal logarithmic mixing of the Thorp shuffle (routing densities), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 238; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Routing-densities-and-representation-contraction-for-Thorp-sweeps-September-26-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/ThorpRouting/Casimir/Main.lean (declaration OAI.ThorpNine.Casimir.Thorp.CasimirBounds.trace_bound)

import Mathlib
import Definitions.Def_ThorpRouting
import Definitions.Def_OAIQ077T001

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.Casimir

namespace Thorp.CasimirBounds
open scoped BigOperators Classical
open UnitaryFinite

lemma trace_bound_q77 (d : ℕ) (μ : YoungDiagram) (e : Card d ≃ Specht.Cell μ) :
    (Module.finrank ℂ (Specht.space μ):ℝ)*traceMoment d μ e 65 ≤
      Real.exp ((1+64*(1+heightDecay 1))*levelScale (2^d) (μ.card-μ.rowLen 0)) := by
  sorry

end Thorp.CasimirBounds

end ThorpNine.Casimir

end OAI
end
