-- Prove2me | Theorems.Thm_OAI_SKValue_split_spatialJet_limit
-- name    : OAI.SKValue.split_spatialJet_limit
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T07:51:10.322347+00:00
-- url     : https://prove2.me/theorems/625f4d0d-0893-4df5-8d31-da52795f7e4d
-- title:
--   OAI.SKValue.split_spatialJet_limit: intermediate lemma from OpenAI, QAOA attains the SK ground-state energy in the thermodynamic-first limit
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SKValue.value_consequences`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *QAOA attains the SK ground-state energy in the thermodynamic-first limit*, OpenAI Math Release, September 25, 2026, result family 281, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SKValue.split_spatialJet_limit` of [lean/OAI/Probability/SKValue/SKValue/Gaussian/SplitJets.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKValue/SKValue/Gaussian/SplitJets.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SKValue`, with `open MeasureTheory ProbabilityTheory Set Filter`, `open scoped Topology NNReal`):
--
--   ```lean
--   lemma split_spatialJet_limit (W:BrownianSpace) (γ:OrderParameter) (t:Ioo (0:ℝ) 1) (k:ℕ) :
--       BoundedUniformLimit (fun n x ↦ spatialJet (γ.coeff t+(gridDelta n:ℝ)) (splitTerminal γ t n) k x)
--         (spatialJet (γ.coeff t) (phi W γ t) k)
--   ```
--
--   **Definitions.** The statement is written with `OAI.SKValue.BoundedUniformLimit`, `OAI.SKValue.gridDelta`, `OAI.SKValue.spatialJet` and `OAI.SKValue.splitTerminal` (definitions bundle `OAIQ4Sk000` of this split); `OAI.SKValue.BrownianSpace`, `OAI.SKValue.OrderParameter` and `OAI.SKValue.phi` (the published bundle `Def_SKValue`).
--
--   **Used by.** The proof of `OAI.SKValue.IsMinimizer.gradient_moment_contact` of this split imports it.
-- source:
--   OpenAI, QAOA attains the SK ground-state energy in the thermodynamic-first limit, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 281; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/QAOA-attains-the-SK-ground-state-energy-in-the-thermodynamic-first-limit-September-25-2026/QAOA-attains-the-SK-ground-state-energy-in-the-thermodynamic-first-limit-September-25-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKValue/SKValue/Gaussian/SplitJets.lean (declaration OAI.SKValue.split_spatialJet_limit)

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
open scoped Topology NNReal
namespace SKValue
lemma split_spatialJet_limit (W:BrownianSpace) (γ:OrderParameter) (t:Ioo (0:ℝ) 1) (k:ℕ) :
    BoundedUniformLimit (fun n x ↦ spatialJet (γ.coeff t+(gridDelta n:ℝ)) (splitTerminal γ t n) k x)
      (spatialJet (γ.coeff t) (phi W γ t) k) := by
  sorry
end SKValue

end

end OAI
end
