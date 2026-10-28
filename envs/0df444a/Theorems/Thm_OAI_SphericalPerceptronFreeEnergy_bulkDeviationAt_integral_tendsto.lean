-- Prove2me | Theorems.Thm_OAI_SphericalPerceptronFreeEnergy_bulkDeviationAt_integral_tendsto
-- name    : OAI.SphericalPerceptronFreeEnergy.bulkDeviationAt_integral_tendsto
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T22:01:51.377344+00:00
-- url     : https://prove2.me/theorems/39cba041-5c1c-47f2-9353-b9c82ff1b7b6
-- title:
--   OAI.SphericalPerceptronFreeEnergy.bulkDeviationAt_integral_tendsto: intermediate lemma from OpenAI, Spherical perceptron free energy (OpenAI result family 222)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SphericalPerceptronFreeEnergy.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Spherical perceptron free energy (OpenAI result family 222)*, OpenAI Math Release, September 24, 2026, result family 222, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SphericalPerceptronFreeEnergy.bulkDeviationAt_integral_tendsto` of [lean/OAI/Probability/Perceptron/Cavity/BulkGoodParameters.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/Perceptron/Cavity/BulkGoodParameters.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SphericalPerceptronFreeEnergy`, with `open MeasureTheory ProbabilityTheory Filter Set`, `open scoped Topology BigOperators BoundedContinuousFunction`):
--
--   ```lean
--   lemma bulkDeviationAt_integral_tendsto (M : ℕ→ℕ) (f : ℝ→ᵇℝ) {A : ℝ}
--       (hA : 0≤A) (hM : ∀ n, (M n:ℝ)≤A*(n+1:ℕ)) (p : ℕ) :
--       Tendsto (fun n => ∫ v, bulkDeviationAt n (M n) f p v ∂bulkParameterLaw) atTop (𝓝 0)
--   ```
--
--   **Definitions.** The statement is written with `OAI.SphericalPerceptronFreeEnergy.bulkDeviationAt` and `OAI.SphericalPerceptronFreeEnergy.bulkParameterLaw` (definitions bundle `OAIQ61Pf000` of this split).
--
--   **Used by.** The proofs of `OAI.SphericalPerceptronFreeEnergy.expectedPressure_lower_smooth` and `OAI.SphericalPerceptronFreeEnergy.omittedBulkDeviation_integral_tendsto` of this split import it.
-- source:
--   OpenAI, Spherical perceptron free energy (OpenAI result family 222), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 222; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/PerceptronFreeEnergy.lean; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/Perceptron/Cavity/BulkGoodParameters.lean (declaration OAI.SphericalPerceptronFreeEnergy.bulkDeviationAt_integral_tendsto)

import Mathlib
import Definitions.Def_OAIQ61Pf000

section

attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

lemma bulkDeviationAt_integral_tendsto (M : ℕ→ℕ) (f : ℝ→ᵇℝ) {A : ℝ}
    (hA : 0≤A) (hM : ∀ n, (M n:ℝ)≤A*(n+1:ℕ)) (p : ℕ) :
    Tendsto (fun n => ∫ v, bulkDeviationAt n (M n) f p v ∂bulkParameterLaw) atTop (𝓝 0) := by
  sorry

end SphericalPerceptronFreeEnergy
end

end OAI
end
