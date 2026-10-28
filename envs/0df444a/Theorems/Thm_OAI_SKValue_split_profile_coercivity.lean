-- Prove2me | Theorems.Thm_OAI_SKValue_split_profile_coercivity
-- name    : OAI.SKValue.split_profile_coercivity
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T07:51:21.619415+00:00
-- url     : https://prove2.me/theorems/93bdb41b-fdd5-488f-8350-16dcb1819c0d
-- title:
--   OAI.SKValue.split_profile_coercivity: intermediate lemma from OpenAI, QAOA attains the SK ground-state energy in the thermodynamic-first limit
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SKValue.value_consequences`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *QAOA attains the SK ground-state energy in the thermodynamic-first limit*, OpenAI Math Release, September 25, 2026, result family 281, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SKValue.split_profile_coercivity` of [lean/OAI/Probability/SKValue/SKValue/Gaussian/SplitShape.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKValue/SKValue/Gaussian/SplitShape.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SKValue`, with `open MeasureTheory ProbabilityTheory Set Filter`, `open scoped Topology NNReal`):
--
--   ```lean
--   lemma split_profile_coercivity (γ:OrderParameter) (t:Ioo (0:ℝ) 1) (n:ℕ) :
--       let A:=splitTerminal γ t n
--       let C:=γ.coeff t+(gridDelta n:ℝ)
--       let l:=γ.splitSegment 0 t t.property.1.le n
--       (1/1000:ℝ)*profileResponse A (fun x ↦ (spatialJet C A 1 x)^4) l 0 0 ≤
--         profileResponse A (fun x ↦ (spatialJet C A 3 x)^2-
--           12*spatialJet C A 1 x*(spatialJet C A 2 x)^2+6*(spatialJet C A 1 x)^4) l 0 0
--   ```
--
--   **Definitions.** The statement is written with `OAI.SKValue.HeatProfile`, `OAI.SKValue.gridDelta`, `OAI.SKValue.profileResponse`, `OAI.SKValue.spatialJet`, `OAI.SKValue.splitTerminal` and `OAI.SKValue.OrderParameter.splitSegment` (definitions bundle `OAIQ4Sk000` of this split); `OAI.SKValue.OrderParameter` (the published bundle `Def_SKValue`).
--
--   **Used by.** The proof of `OAI.SKValue.IsMinimizer.gradient_moment_contact` of this split imports it.
-- source:
--   OpenAI, QAOA attains the SK ground-state energy in the thermodynamic-first limit, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 281; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/QAOA-attains-the-SK-ground-state-energy-in-the-thermodynamic-first-limit-September-25-2026/QAOA-attains-the-SK-ground-state-energy-in-the-thermodynamic-first-limit-September-25-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKValue/SKValue/Gaussian/SplitShape.lean (declaration OAI.SKValue.split_profile_coercivity)

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
lemma split_profile_coercivity (γ:OrderParameter) (t:Ioo (0:ℝ) 1) (n:ℕ) :
    let A:=splitTerminal γ t n
    let C:=γ.coeff t+(gridDelta n:ℝ)
    let l:=γ.splitSegment 0 t t.property.1.le n
    (1/1000:ℝ)*profileResponse A (fun x ↦ (spatialJet C A 1 x)^4) l 0 0 ≤
      profileResponse A (fun x ↦ (spatialJet C A 3 x)^2-
        12*spatialJet C A 1 x*(spatialJet C A 2 x)^2+6*(spatialJet C A 1 x)^4) l 0 0 := by
  sorry
end SKValue

end

end OAI
end
