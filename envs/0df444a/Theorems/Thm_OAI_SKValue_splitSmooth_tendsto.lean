-- Prove2me | Theorems.Thm_OAI_SKValue_splitSmooth_tendsto
-- name    : OAI.SKValue.splitSmooth_tendsto
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T07:51:14.615838+00:00
-- url     : https://prove2.me/theorems/aab67fcc-fc80-4ed3-b6a3-3f302b4f25d3
-- title:
--   OAI.SKValue.splitSmooth_tendsto: intermediate lemma from OpenAI, QAOA attains the SK ground-state energy in the thermodynamic-first limit
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SKValue.value_consequences`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *QAOA attains the SK ground-state energy in the thermodynamic-first limit*, OpenAI Math Release, September 25, 2026, result family 281, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SKValue.splitSmooth_tendsto` of [lean/OAI/Probability/SKValue/SKValue/Gaussian/SplitConvergence.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKValue/SKValue/Gaussian/SplitConvergence.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SKValue`, with `open MeasureTheory ProbabilityTheory Set Filter`, `open scoped Topology NNReal ContDiff`):
--
--   ```lean
--   lemma splitSmooth_tendsto (W:BrownianSpace) (γ:OrderParameter) (t:Ioo (0:ℝ) 1) :
--       TendstoUniformly (fun n (p:Ico (0:ℝ) 1×ℝ) ↦ splitSmooth γ t n p.1 p.2)
--         (fun p ↦ phi W γ p.1 p.2) atTop
--   ```
--
--   **Definitions.** The statement is written with `OAI.SKValue.splitSmooth` (definitions bundle `OAIQ4Sk000` of this split); `OAI.SKValue.BrownianSpace`, `OAI.SKValue.OrderParameter` and `OAI.SKValue.phi` (the published bundle `Def_SKValue`).
--
--   **Used by.** The proofs of `OAI.SKValue.IsDiffusion.splitResponse_tendsto` and `OAI.SKValue.split_spatialJet_limit` of this split import it.
-- source:
--   OpenAI, QAOA attains the SK ground-state energy in the thermodynamic-first limit, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 281; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/QAOA-attains-the-SK-ground-state-energy-in-the-thermodynamic-first-limit-September-25-2026/QAOA-attains-the-SK-ground-state-energy-in-the-thermodynamic-first-limit-September-25-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKValue/SKValue/Gaussian/SplitConvergence.lean (declaration OAI.SKValue.splitSmooth_tendsto)

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
lemma splitSmooth_tendsto (W:BrownianSpace) (γ:OrderParameter) (t:Ioo (0:ℝ) 1) :
    TendstoUniformly (fun n (p:Ico (0:ℝ) 1×ℝ) ↦ splitSmooth γ t n p.1 p.2)
      (fun p ↦ phi W γ p.1 p.2) atTop := by
  sorry
end SKValue

end

end OAI
end
