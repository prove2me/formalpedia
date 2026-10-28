-- Prove2me | Theorems.Thm_OAI_SKValue_IsDiffusion_splitResponse_tendsto
-- name    : OAI.SKValue.IsDiffusion.splitResponse_tendsto
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T07:48:55.348988+00:00
-- url     : https://prove2.me/theorems/dae16918-18e9-47a5-b4b7-0f4408d4e182
-- title:
--   OAI.SKValue.IsDiffusion.splitResponse_tendsto: intermediate lemma from OpenAI, QAOA attains the SK ground-state energy in the thermodynamic-first limit
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SKValue.value_consequences`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *QAOA attains the SK ground-state energy in the thermodynamic-first limit*, OpenAI Math Release, September 25, 2026, result family 281, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SKValue.IsDiffusion.splitResponse_tendsto` of [lean/OAI/Probability/SKValue/SKValue/Gaussian/UniformError.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKValue/SKValue/Gaussian/UniformError.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SKValue`, with `open MeasureTheory ProbabilityTheory Set Filter`, `open scoped Topology NNReal ContDiff`):
--
--   ```lean
--   lemma IsDiffusion.splitResponse_tendsto {W:BrownianSpace} {γ:OrderParameter} {X:ℝ → W.Ω → ℝ}
--       (hX:IsDiffusion W γ X) (t:Ioo (0:ℝ) 1) {f:ℝ → ℝ} (hf:BoundedSmooth f) :
--       Tendsto (fun n ↦ profileResponse (splitTerminal γ t n) f (γ.splitSegment 0 t t.property.1.le n) 0 0)
--         atTop (𝓝 (MeasureTheory.integral W.μ (fun z ↦ f (X t z))))
--   ```
--
--   **Definitions.** The statement is written with `OAI.SKValue.BoundedSmooth`, `OAI.SKValue.profileResponse`, `OAI.SKValue.splitTerminal` and `OAI.SKValue.OrderParameter.splitSegment` (definitions bundle `OAIQ4Sk000` of this split); `OAI.SKValue.BrownianSpace`, `OAI.SKValue.IsDiffusion` and `OAI.SKValue.OrderParameter` (the published bundle `Def_SKValue`).
--
--   **Used by.** The proof of `OAI.SKValue.IsMinimizer.gradient_moment_contact` of this split imports it.
-- source:
--   OpenAI, QAOA attains the SK ground-state energy in the thermodynamic-first limit, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 281; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/QAOA-attains-the-SK-ground-state-energy-in-the-thermodynamic-first-limit-September-25-2026/QAOA-attains-the-SK-ground-state-energy-in-the-thermodynamic-first-limit-September-25-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKValue/SKValue/Gaussian/UniformError.lean (declaration OAI.SKValue.IsDiffusion.splitResponse_tendsto)

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
open scoped Topology NNReal ContDiff
namespace SKValue

lemma IsDiffusion.splitResponse_tendsto {W:BrownianSpace} {γ:OrderParameter} {X:ℝ → W.Ω → ℝ}
    (hX:IsDiffusion W γ X) (t:Ioo (0:ℝ) 1) {f:ℝ → ℝ} (hf:BoundedSmooth f) :
    Tendsto (fun n ↦ profileResponse (splitTerminal γ t n) f (γ.splitSegment 0 t t.property.1.le n) 0 0)
      atTop (𝓝 (MeasureTheory.integral W.μ (fun z ↦ f (X t z)))) := by
  sorry
end SKValue

end

end OAI
end
