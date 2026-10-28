-- Prove2me | Theorems.Thm_OAI_SKValue_IsMinimizer_moment_eq_at_contact
-- name    : OAI.SKValue.IsMinimizer.moment_eq_at_contact
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T07:49:19.607457+00:00
-- url     : https://prove2.me/theorems/a82486ca-2201-44c8-a9b1-601dfdd29592
-- title:
--   OAI.SKValue.IsMinimizer.moment_eq_at_contact: intermediate lemma from OpenAI, QAOA attains the SK ground-state energy in the thermodynamic-first limit
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SKValue.value_consequences`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *QAOA attains the SK ground-state energy in the thermodynamic-first limit*, OpenAI Math Release, September 25, 2026, result family 281, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SKValue.IsMinimizer.moment_eq_at_contact` of [lean/OAI/Probability/SKValue/SKValue/Variation/ContactVariations.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKValue/SKValue/Variation/ContactVariations.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SKValue`, with `open MeasureTheory ProbabilityTheory Set Filter`, `open scoped Topology NNReal ENNReal BigOperators`):
--
--   ```lean
--   lemma IsMinimizer.moment_eq_at_contact {W : BrownianSpace} {γ : OrderParameter}
--       {X : ℝ → W.Ω → ℝ} (hγ : IsMinimizer W γ) (hX : IsDiffusion W γ X)
--       {s : ℝ} (hs : s∈Ioo (0 : ℝ) 1) (hG : contactPotential W γ X s=0) :
--       gradientMoment W γ X s=s
--   ```
--
--   **Definitions.** The statement is written with `OAI.SKValue.contactPotential` and `OAI.SKValue.gradientMoment` (definitions bundle `OAIQ4Sk000` of this split); `OAI.SKValue.BrownianSpace`, `OAI.SKValue.IsDiffusion`, `OAI.SKValue.IsMinimizer` and `OAI.SKValue.OrderParameter` (the published bundle `Def_SKValue`).
--
--   **Used by.** The proof of `OAI.SKValue.IsMinimizer.gradient_moment_contact` of this split imports it.
-- source:
--   OpenAI, QAOA attains the SK ground-state energy in the thermodynamic-first limit, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 281; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/QAOA-attains-the-SK-ground-state-energy-in-the-thermodynamic-first-limit-September-25-2026/QAOA-attains-the-SK-ground-state-energy-in-the-thermodynamic-first-limit-September-25-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKValue/SKValue/Variation/ContactVariations.lean (declaration OAI.SKValue.IsMinimizer.moment_eq_at_contact)

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

lemma IsMinimizer.moment_eq_at_contact {W : BrownianSpace} {γ : OrderParameter}
    {X : ℝ → W.Ω → ℝ} (hγ : IsMinimizer W γ) (hX : IsDiffusion W γ X)
    {s : ℝ} (hs : s∈Ioo (0 : ℝ) 1) (hG : contactPotential W γ X s=0) :
    gradientMoment W γ X s=s := by
  sorry

end SKValue

end

end OAI
end
