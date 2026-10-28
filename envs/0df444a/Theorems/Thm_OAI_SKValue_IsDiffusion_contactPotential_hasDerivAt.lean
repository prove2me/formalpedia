-- Prove2me | Theorems.Thm_OAI_SKValue_IsDiffusion_contactPotential_hasDerivAt
-- name    : OAI.SKValue.IsDiffusion.contactPotential_hasDerivAt
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T07:46:40.730476+00:00
-- url     : https://prove2.me/theorems/2e0b17d4-5c2e-47e0-950e-5cb74bc9ce9b
-- title:
--   OAI.SKValue.IsDiffusion.contactPotential_hasDerivAt: intermediate lemma from OpenAI, QAOA attains the SK ground-state energy in the thermodynamic-first limit
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SKValue.value_consequences`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *QAOA attains the SK ground-state energy in the thermodynamic-first limit*, OpenAI Math Release, September 25, 2026, result family 281, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SKValue.IsDiffusion.contactPotential_hasDerivAt` of [lean/OAI/Probability/SKValue/SKValue/Variation/ContactVariations.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKValue/SKValue/Variation/ContactVariations.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SKValue`, with `open MeasureTheory ProbabilityTheory Set Filter`, `open scoped Topology NNReal ENNReal BigOperators`):
--
--   ```lean
--   lemma IsDiffusion.contactPotential_hasDerivAt {W : BrownianSpace} {γ : OrderParameter}
--       {X : ℝ → W.Ω → ℝ} (hX : IsDiffusion W γ X) {s : ℝ} (hs : s∈Ioo (0 : ℝ) 1) :
--       HasDerivAt (contactPotential W γ X) (s-gradientMoment W γ X s) s
--   ```
--
--   **Definitions.** The statement is written with `OAI.SKValue.contactPotential` and `OAI.SKValue.gradientMoment` (definitions bundle `OAIQ4Sk000` of this split); `OAI.SKValue.BrownianSpace`, `OAI.SKValue.IsDiffusion` and `OAI.SKValue.OrderParameter` (the published bundle `Def_SKValue`).
--
--   **Used by.** The proofs of `OAI.SKValue.IsMinimizer.gradient_moment_contact` and `OAI.SKValue.IsMinimizer.moment_eq_at_contact` of this split import it.
-- source:
--   OpenAI, QAOA attains the SK ground-state energy in the thermodynamic-first limit, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 281; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/QAOA-attains-the-SK-ground-state-energy-in-the-thermodynamic-first-limit-September-25-2026/QAOA-attains-the-SK-ground-state-energy-in-the-thermodynamic-first-limit-September-25-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKValue/SKValue/Variation/ContactVariations.lean (declaration OAI.SKValue.IsDiffusion.contactPotential_hasDerivAt)

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

lemma IsDiffusion.contactPotential_hasDerivAt {W : BrownianSpace} {γ : OrderParameter}
    {X : ℝ → W.Ω → ℝ} (hX : IsDiffusion W γ X) {s : ℝ} (hs : s∈Ioo (0 : ℝ) 1) :
    HasDerivAt (contactPotential W γ X) (s-gradientMoment W γ X s) s := by
  sorry

end SKValue

end

end OAI
end
