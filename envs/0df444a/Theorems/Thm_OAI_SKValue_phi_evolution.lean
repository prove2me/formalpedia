-- Prove2me | Theorems.Thm_OAI_SKValue_phi_evolution
-- name    : OAI.SKValue.phi_evolution
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T07:50:47.364392+00:00
-- url     : https://prove2.me/theorems/881fa8f3-0099-4c0e-803a-8f0d83b7cbf7
-- title:
--   OAI.SKValue.phi_evolution: intermediate lemma from OpenAI, QAOA attains the SK ground-state energy in the thermodynamic-first limit
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SKValue.value_consequences`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *QAOA attains the SK ground-state energy in the thermodynamic-first limit*, OpenAI Math Release, September 25, 2026, result family 281, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SKValue.phi_evolution` of [lean/OAI/Probability/SKValue/SKValue/Control/PhiRegularity.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKValue/SKValue/Control/PhiRegularity.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SKValue`, with `open MeasureTheory ProbabilityTheory Set Filter`, `open scoped Topology NNReal ENNReal BigOperators ContDiff`):
--
--   ```lean
--   lemma phi_evolution (W : BrownianSpace) (γ : OrderParameter) {S : ℝ}
--       (hS : S∈Ico (0 : ℝ) 1) : SmoothEvolution S γ.coeff (phi W γ)
--   ```
--
--   **Definitions.** The statement is written with `OAI.SKValue.SmoothEvolution` (definitions bundle `OAIQ4Sk000` of this split); `OAI.SKValue.BrownianSpace`, `OAI.SKValue.OrderParameter` and `OAI.SKValue.phi` (the published bundle `Def_SKValue`).
--
--   **Used by.** The proofs of `OAI.SKValue.IsDiffusion.curvatureExpr_hasDerivAt`, `OAI.SKValue.IsDiffusion.curvatureSlope_hasDerivAt`, `OAI.SKValue.IsDiffusion.momentExpr_hasDerivAt`, `OAI.SKValue.IsMinimizer.gradient_moment_contact`, `OAI.SKValue.sourceStripRegularity` and `OAI.SKValue.value_consequences` of this split import it.
-- source:
--   OpenAI, QAOA attains the SK ground-state energy in the thermodynamic-first limit, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 281; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/QAOA-attains-the-SK-ground-state-energy-in-the-thermodynamic-first-limit-September-25-2026/QAOA-attains-the-SK-ground-state-energy-in-the-thermodynamic-first-limit-September-25-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKValue/SKValue/Control/PhiRegularity.lean (declaration OAI.SKValue.phi_evolution)

import Mathlib
import Definitions.Def_SKValue
import Definitions.Def_OAIQ4Sk000

section

attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators ContDiff
namespace SKValue

lemma phi_evolution (W : BrownianSpace) (γ : OrderParameter) {S : ℝ}
    (hS : S∈Ico (0 : ℝ) 1) : SmoothEvolution S γ.coeff (phi W γ) := by
  sorry

end SKValue

end

end OAI
end
