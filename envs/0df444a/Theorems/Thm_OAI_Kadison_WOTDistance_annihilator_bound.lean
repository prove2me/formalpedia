-- Prove2me | Theorems.Thm_OAI_Kadison_WOTDistance_annihilator_bound
-- name    : OAI.Kadison.WOTDistance.annihilator_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T06:50:08.404979+00:00
-- url     : https://prove2.me/theorems/1d445093-cd5a-4ae2-a96e-0a7b7bbf0f31
-- title:
--   OAI.Kadison.WOTDistance.annihilator_bound: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Kadison.WOTDistance`, with `open scoped BigOperators InnerProductSpace`, `open ContinuousLinearMapWOT`, `open OperatorAmplification`):
--
--   ```lean
--   theorem annihilator_bound (M : VonNeumannAlgebra H) (G : H →L[ℂ] H)
--       {c : ℝ} (hc : 0 ≤ c) (hcb : AmplifiedBound M G c)
--       (φ : (H →WOT[ℂ] H) →L[ℂ] ℂ)
--       (hφ : ∀ T∈M.commutant, φ (ofCLM T)=0) :
--       ‖φ (ofCLM G)‖ ≤ c*‖φ.comp ContinuousLinearMap.WOTofCLM‖
--   ```
--
--   **Definitions.** The statement is written with `OAI.Kadison.WOTDistance.AmplifiedBound` (definitions bundle `OAIQ039C031` of this split).
--
--   **Used by.** The proof of `OAI.Kadison.WOTDistance.exists_commutant_approximation` of this split imports it.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ039C031

section

attribute [-instance] _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped BigOperators InnerProductSpace

open ContinuousLinearMapWOT

namespace Kadison.WOTDistance

open OperatorAmplification

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem annihilator_bound (M : VonNeumannAlgebra H) (G : H →L[ℂ] H)
    {c : ℝ} (hc : 0 ≤ c) (hcb : AmplifiedBound M G c)
    (φ : (H →WOT[ℂ] H) →L[ℂ] ℂ)
    (hφ : ∀ T∈M.commutant, φ (ofCLM T)=0) :
    ‖φ (ofCLM G)‖ ≤ c*‖φ.comp ContinuousLinearMap.WOTofCLM‖ := by
  sorry

end Kadison.WOTDistance

end

end
end

end OAI
end
