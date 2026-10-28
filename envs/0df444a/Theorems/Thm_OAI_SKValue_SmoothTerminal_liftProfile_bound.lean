-- Prove2me | Theorems.Thm_OAI_SKValue_SmoothTerminal_liftProfile_bound
-- name    : OAI.SKValue.SmoothTerminal.liftProfile_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T07:49:22.676003+00:00
-- url     : https://prove2.me/theorems/144805c0-ddac-4709-88eb-38030ff055f1
-- title:
--   OAI.SKValue.SmoothTerminal.liftProfile_bound: intermediate lemma from OpenAI, QAOA attains the SK ground-state energy in the thermodynamic-first limit
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SKValue.value_consequences`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *QAOA attains the SK ground-state energy in the thermodynamic-first limit*, OpenAI Math Release, September 25, 2026, result family 281, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SKValue.SmoothTerminal.liftProfile_bound` of [lean/OAI/Probability/SKValue/SKValue/Equations/StrictProfile.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKValue/SKValue/Equations/StrictProfile.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SKValue`, with `open MeasureTheory ProbabilityTheory Filter Set`, `open scoped Topology NNReal ENNReal BigOperators`):
--
--   ```lean
--   lemma SmoothTerminal.liftProfile_bound (W : BrownianSpace) {ψ : ℝ → ℝ} (hψ : SmoothTerminal ψ)
--       {l : HeatProfile} (hl : l.Pairwise (fun p r ↦ p.2 ≤ r.2)) (hT : profileTime l=1)
--       {ε : ℝ≥0} (hε : 0<ε) (k : ℕ) (x : ℝ) :
--       |profileValue ψ (liftProfile ε k l) 0 x-profileValue ψ l 0 x|≤(3/2 : ℝ)*(ε : ℝ)*(k+l.length)
--   ```
--
--   **Definitions.** The statement is written with `OAI.SKValue.HeatProfile`, `OAI.SKValue.SmoothTerminal`, `OAI.SKValue.liftProfile`, `OAI.SKValue.profileTime` and `OAI.SKValue.profileValue` (definitions bundle `OAIQ4Sk000` of this split); `OAI.SKValue.BrownianSpace` (the published bundle `Def_SKValue`).
--
--   **Used by.** The proof of `OAI.SKValueG.weak_profile_guerra_upper` of this split imports it.
-- source:
--   OpenAI, QAOA attains the SK ground-state energy in the thermodynamic-first limit, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 281; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/QAOA-attains-the-SK-ground-state-energy-in-the-thermodynamic-first-limit-September-25-2026/QAOA-attains-the-SK-ground-state-energy-in-the-thermodynamic-first-limit-September-25-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKValue/SKValue/Equations/StrictProfile.lean (declaration OAI.SKValue.SmoothTerminal.liftProfile_bound)

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

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators
namespace SKValue

lemma SmoothTerminal.liftProfile_bound (W : BrownianSpace) {ψ : ℝ → ℝ} (hψ : SmoothTerminal ψ)
    {l : HeatProfile} (hl : l.Pairwise (fun p r ↦ p.2 ≤ r.2)) (hT : profileTime l=1)
    {ε : ℝ≥0} (hε : 0<ε) (k : ℕ) (x : ℝ) :
    |profileValue ψ (liftProfile ε k l) 0 x-profileValue ψ l 0 x|≤(3/2 : ℝ)*(ε : ℝ)*(k+l.length) := by
  sorry

end SKValue

end

end OAI
end
