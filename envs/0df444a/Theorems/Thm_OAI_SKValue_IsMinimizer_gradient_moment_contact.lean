-- Prove2me | Theorems.Thm_OAI_SKValue_IsMinimizer_gradient_moment_contact
-- name    : OAI.SKValue.IsMinimizer.gradient_moment_contact
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T07:44:39.467668+00:00
-- url     : https://prove2.me/theorems/9b420fd5-0e72-4293-9fd2-acf913a196b8
-- title:
--   OAI.SKValue.IsMinimizer.gradient_moment_contact: intermediate lemma from OpenAI, QAOA attains the SK ground-state energy in the thermodynamic-first limit
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SKValue.value_consequences`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *QAOA attains the SK ground-state energy in the thermodynamic-first limit*, OpenAI Math Release, September 25, 2026, result family 281, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SKValue.IsMinimizer.gradient_moment_contact` of [lean/OAI/Probability/SKValue/SKValue/Variation/MinimizerContact.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKValue/SKValue/Variation/MinimizerContact.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SKValue`, with `open MeasureTheory ProbabilityTheory Set Filter`, `open scoped Topology NNReal`):
--
--   ```lean
--   theorem IsMinimizer.gradient_moment_contact {W:BrownianSpace} {γ:OrderParameter} {X:ℝ → W.Ω → ℝ}
--       (hγ:IsMinimizer W γ) (hX:IsDiffusion W γ X):
--       ∀t∈Ico (0:ℝ) 1,(∫ z,(gradient W γ t (X t z))^2 ∂W.μ)=t
--   ```
--
--   **Definitions.** The statement is written with `OAI.SKValue.BrownianSpace`, `OAI.SKValue.IsDiffusion`, `OAI.SKValue.IsMinimizer`, `OAI.SKValue.OrderParameter` and `OAI.SKValue.gradient` (the published bundle `Def_SKValue`).
--
--   **Used by.** The proof of `OAI.SKValue.value_consequences` of this split imports it.
-- source:
--   OpenAI, QAOA attains the SK ground-state energy in the thermodynamic-first limit, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 281; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/QAOA-attains-the-SK-ground-state-energy-in-the-thermodynamic-first-limit-September-25-2026/QAOA-attains-the-SK-ground-state-energy-in-the-thermodynamic-first-limit-September-25-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKValue/SKValue/Variation/MinimizerContact.lean (declaration OAI.SKValue.IsMinimizer.gradient_moment_contact)

import Mathlib
import Definitions.Def_SKValue

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal
namespace SKValue

theorem IsMinimizer.gradient_moment_contact {W:BrownianSpace} {γ:OrderParameter} {X:ℝ → W.Ω → ℝ}
    (hγ:IsMinimizer W γ) (hX:IsDiffusion W γ X):
    ∀t∈Ico (0:ℝ) 1,(∫ z,(gradient W γ t (X t z))^2 ∂W.μ)=t := by
  sorry
end SKValue

end

end OAI
end
