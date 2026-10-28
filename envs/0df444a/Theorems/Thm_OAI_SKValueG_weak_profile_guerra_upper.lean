-- Prove2me | Theorems.Thm_OAI_SKValueG_weak_profile_guerra_upper
-- name    : OAI.SKValueG.weak_profile_guerra_upper
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T07:51:35.533515+00:00
-- url     : https://prove2.me/theorems/f477c237-203f-4e26-8f92-1c13e4f6a4d2
-- title:
--   OAI.SKValueG.weak_profile_guerra_upper: intermediate lemma from OpenAI, QAOA attains the SK ground-state energy in the thermodynamic-first limit
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SKValue.value_consequences`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *QAOA attains the SK ground-state energy in the thermodynamic-first limit*, OpenAI Math Release, September 25, 2026, result family 281, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SKValueG.weak_profile_guerra_upper` of [lean/OAI/Probability/SKValue/SKValue/GroundState/WeakGuerra.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKValue/SKValue/GroundState/WeakGuerra.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SKValueG`, with `open MeasureTheory ProbabilityTheory Filter Set`, `open scoped Topology NNReal ENNReal BigOperators`):
--
--   ```lean
--   lemma weak_profile_guerra_upper (W : SKValue.BrownianSpace) {n : ℕ} (hn : 0<n)
--       {ψ : ℝ → ℝ} (hψ : SKValue.SmoothTerminal ψ) (hb : ∀ x,|x|≤ψ x)
--       {l : SKValue.HeatProfile} (hl : l.Pairwise (fun p r ↦ p.2 ≤ r.2)) (hT : SKValue.profileTime l=1) :
--       expectedMaximum n ≤ (n : ℝ)*(SKValue.profileValue ψ l 0 0-
--         (1/2 : ℝ)*(∫ t in (0 : ℝ)..1,t*SKValue.profileCoeff l t))
--   ```
--
--   **Definitions.** The statement is written with `OAI.SKValue.HeatProfile`, `OAI.SKValue.SmoothTerminal`, `OAI.SKValue.profileCoeff`, `OAI.SKValue.profileTime`, `OAI.SKValue.profileValue` and `OAI.SKValueG.expectedMaximum` (definitions bundle `OAIQ4Sk000` of this split); `OAI.SKValue.BrownianSpace` (the published bundle `Def_SKValue`).
--
--   **Used by.** The proof of `OAI.SKValue.value_consequences` of this split imports it.
-- source:
--   OpenAI, QAOA attains the SK ground-state energy in the thermodynamic-first limit, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 281; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/QAOA-attains-the-SK-ground-state-energy-in-the-thermodynamic-first-limit-September-25-2026/QAOA-attains-the-SK-ground-state-energy-in-the-thermodynamic-first-limit-September-25-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKValue/SKValue/GroundState/WeakGuerra.lean (declaration OAI.SKValueG.weak_profile_guerra_upper)

import Mathlib
import Definitions.Def_SKValue
import Definitions.Def_OAIQ4Sk000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators
namespace SKValueG

lemma weak_profile_guerra_upper (W : SKValue.BrownianSpace) {n : ℕ} (hn : 0<n)
    {ψ : ℝ → ℝ} (hψ : SKValue.SmoothTerminal ψ) (hb : ∀ x,|x|≤ψ x)
    {l : SKValue.HeatProfile} (hl : l.Pairwise (fun p r ↦ p.2 ≤ r.2)) (hT : SKValue.profileTime l=1) :
    expectedMaximum n ≤ (n : ℝ)*(SKValue.profileValue ψ l 0 0-
      (1/2 : ℝ)*(∫ t in (0 : ℝ)..1,t*SKValue.profileCoeff l t)) := by
  sorry

end SKValueG

end

end OAI
end
