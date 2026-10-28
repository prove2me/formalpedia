-- Prove2me | Theorems.Thm_OAI_SphericalPerceptronFreeEnergy_indexedDepthLaw_pair_weights
-- name    : OAI.SphericalPerceptronFreeEnergy.indexedDepthLaw_pair_weights
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T22:07:30.835314+00:00
-- url     : https://prove2.me/theorems/e4d1523b-dbb7-4cec-9340-c6df1566fbec
-- title:
--   OAI.SphericalPerceptronFreeEnergy.indexedDepthLaw_pair_weights: intermediate lemma from OpenAI, Spherical perceptron free energy (OpenAI result family 222)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SphericalPerceptronFreeEnergy.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Spherical perceptron free energy (OpenAI result family 222)*, OpenAI Math Release, September 24, 2026, result family 222, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SphericalPerceptronFreeEnergy.indexedDepthLaw_pair_weights` of [lean/OAI/Probability/Perceptron/Cascade/DepthWeights.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/Perceptron/Cascade/DepthWeights.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SphericalPerceptronFreeEnergy`, with `open MeasureTheory ProbabilityTheory Set Filter`, `open scoped Classical ENNReal NNReal BigOperators Topology`):
--
--   ```lean
--   theorem indexedDepthLaw_pair_weights (k : ℕ) (w : Fin (k+1) → ℝ)
--       (hw : ∀ i, 0 < w i) (hw1 : ∑ i, w i = 1) (c : Fin (k+1)) :
--       (indexedDepthLaw k (stepCumulative w) : Measure (FiniteOverlap (Fin (k+1)))).real
--         {R | R 0 1 = c} = w c
--   ```
--
--   **Definitions.** The statement is written with `OAI.SphericalPerceptronFreeEnergy.FiniteOverlap`, `OAI.SphericalPerceptronFreeEnergy.indexedDepthLaw` and `OAI.SphericalPerceptronFreeEnergy.stepCumulative` (definitions bundle `OAIQ61Pf000` of this split).
--
--   **Used by.** The proof of `OAI.SphericalPerceptronFreeEnergy.bulk_cavity_data` of this split imports it.
-- source:
--   OpenAI, Spherical perceptron free energy (OpenAI result family 222), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 222; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/PerceptronFreeEnergy.lean; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/Perceptron/Cascade/DepthWeights.lean (declaration OAI.SphericalPerceptronFreeEnergy.indexedDepthLaw_pair_weights)

import Mathlib
import Definitions.Def_OAIQ61Pf000

section

attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical ENNReal NNReal BigOperators Topology
namespace SphericalPerceptronFreeEnergy

theorem indexedDepthLaw_pair_weights (k : ℕ) (w : Fin (k+1) → ℝ)
    (hw : ∀ i, 0 < w i) (hw1 : ∑ i, w i = 1) (c : Fin (k+1)) :
    (indexedDepthLaw k (stepCumulative w) : Measure (FiniteOverlap (Fin (k+1)))).real
      {R | R 0 1 = c} = w c := by
  sorry

end SphericalPerceptronFreeEnergy

end

end OAI
end
