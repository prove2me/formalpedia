-- Prove2me | Theorems.Thm_OAI_SKValue_smoothApprox_tendsto
-- name    : OAI.SKValue.smoothApprox_tendsto
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T07:51:03.116002+00:00
-- url     : https://prove2.me/theorems/878ad97e-eac3-4f99-a0f8-1d7aef1b4a9f
-- title:
--   OAI.SKValue.smoothApprox_tendsto: intermediate lemma from OpenAI, QAOA attains the SK ground-state energy in the thermodynamic-first limit
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SKValue.value_consequences`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *QAOA attains the SK ground-state energy in the thermodynamic-first limit*, OpenAI Math Release, September 25, 2026, result family 281, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SKValue.smoothApprox_tendsto` of [lean/OAI/Probability/SKValue/SKValue/Evolution/GridConvergence.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKValue/SKValue/Evolution/GridConvergence.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SKValue`, with `open MeasureTheory ProbabilityTheory Set Filter`, `open scoped Topology NNReal ENNReal BigOperators`):
--
--   ```lean
--   lemma smoothApprox_tendsto (W : BrownianSpace) (γ : OrderParameter) :
--       TendstoUniformly (fun n (p : Ico (0 : ℝ) 1×ℝ) ↦ smoothApprox γ n p.1 p.2)
--         (fun p ↦ phi W γ p.1 p.2) atTop
--   ```
--
--   **Definitions.** The statement is written with `OAI.SKValue.smoothApprox` (definitions bundle `OAIQ4Sk000` of this split); `OAI.SKValue.BrownianSpace`, `OAI.SKValue.OrderParameter` and `OAI.SKValue.phi` (the published bundle `Def_SKValue`).
--
--   **Used by.** The proofs of `OAI.SKValue.IsMinimizer.gradient_moment_contact`, `OAI.SKValue.phi_evolution`, `OAI.SKValue.phi_gradient_difference_bound`, `OAI.SKValue.sourceStripRegularity` and `OAI.SKValue.value_consequences` of this split import it.
-- source:
--   OpenAI, QAOA attains the SK ground-state energy in the thermodynamic-first limit, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 281; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/QAOA-attains-the-SK-ground-state-energy-in-the-thermodynamic-first-limit-September-25-2026/QAOA-attains-the-SK-ground-state-energy-in-the-thermodynamic-first-limit-September-25-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKValue/SKValue/Evolution/GridConvergence.lean (declaration OAI.SKValue.smoothApprox_tendsto)

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
open scoped Topology NNReal ENNReal BigOperators
namespace SKValue

lemma smoothApprox_tendsto (W : BrownianSpace) (γ : OrderParameter) :
    TendstoUniformly (fun n (p : Ico (0 : ℝ) 1×ℝ) ↦ smoothApprox γ n p.1 p.2)
      (fun p ↦ phi W γ p.1 p.2) atTop := by
  sorry

end SKValue

end

end OAI
end
