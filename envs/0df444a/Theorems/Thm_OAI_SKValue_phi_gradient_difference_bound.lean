-- Prove2me | Theorems.Thm_OAI_SKValue_phi_gradient_difference_bound
-- name    : OAI.SKValue.phi_gradient_difference_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T07:44:40.942988+00:00
-- url     : https://prove2.me/theorems/1d8c92af-e308-43af-ba99-9f80ae1d5b56
-- title:
--   OAI.SKValue.phi_gradient_difference_bound: intermediate lemma from OpenAI, QAOA attains the SK ground-state energy in the thermodynamic-first limit
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SKValue.value_consequences`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *QAOA attains the SK ground-state energy in the thermodynamic-first limit*, OpenAI Math Release, September 25, 2026, result family 281, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SKValue.phi_gradient_difference_bound` of [lean/OAI/Probability/SKValue/SKValue/Variation/WeightedMoments.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKValue/SKValue/Variation/WeightedMoments.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SKValue`, with `open MeasureTheory ProbabilityTheory Set Filter`, `open scoped Topology NNReal ENNReal BigOperators`):
--
--   ```lean
--   lemma phi_gradient_difference_bound (W : BrownianSpace) (γ β : OrderParameter)
--       {T L ε h : ℝ} (hT : T∈Ico (0 : ℝ) 1)
--       (hL : ∀ t∈Icc (0 : ℝ) T,∀ x y,|gradient W γ t x-gradient W γ t y|≤L*|x-y|)
--       (he : ∀ t∈Icc (0 : ℝ) T,∀ x,|phi W β t x-phi W γ t x|≤ε)
--       (hh : 0<h) {t : ℝ} (ht : t∈Icc (0 : ℝ) T) (x : ℝ) :
--       |gradient W β t x-gradient W γ t x|≤L*h+2*ε/h
--   ```
--
--   **Definitions.** The statement is written with `OAI.SKValue.BrownianSpace`, `OAI.SKValue.OrderParameter`, `OAI.SKValue.gradient` and `OAI.SKValue.phi` (the published bundle `Def_SKValue`).
--
--   **Used by.** The proofs of `OAI.SKValue.IsMinimizer.coeff_constant_of_contactPositive`, `OAI.SKValue.IsMinimizer.contactPotential_nonneg` and `OAI.SKValue.IsMinimizer.contact_origin_of_positive` of this split import it.
-- source:
--   OpenAI, QAOA attains the SK ground-state energy in the thermodynamic-first limit, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 281; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/QAOA-attains-the-SK-ground-state-energy-in-the-thermodynamic-first-limit-September-25-2026/QAOA-attains-the-SK-ground-state-energy-in-the-thermodynamic-first-limit-September-25-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKValue/SKValue/Variation/WeightedMoments.lean (declaration OAI.SKValue.phi_gradient_difference_bound)

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
open scoped Topology NNReal ENNReal BigOperators
namespace SKValue

lemma phi_gradient_difference_bound (W : BrownianSpace) (γ β : OrderParameter)
    {T L ε h : ℝ} (hT : T∈Ico (0 : ℝ) 1)
    (hL : ∀ t∈Icc (0 : ℝ) T,∀ x y,|gradient W γ t x-gradient W γ t y|≤L*|x-y|)
    (he : ∀ t∈Icc (0 : ℝ) T,∀ x,|phi W β t x-phi W γ t x|≤ε)
    (hh : 0<h) {t : ℝ} (ht : t∈Icc (0 : ℝ) T) (x : ℝ) :
    |gradient W β t x-gradient W γ t x|≤L*h+2*ε/h := by
  sorry

end SKValue

end

end OAI
end
