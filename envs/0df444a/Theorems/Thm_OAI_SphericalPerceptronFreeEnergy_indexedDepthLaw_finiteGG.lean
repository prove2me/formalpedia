-- Prove2me | Theorems.Thm_OAI_SphericalPerceptronFreeEnergy_indexedDepthLaw_finiteGG
-- name    : OAI.SphericalPerceptronFreeEnergy.indexedDepthLaw_finiteGG
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T22:07:08.528237+00:00
-- url     : https://prove2.me/theorems/a81d3544-b6c7-475f-a55f-0f24ab52e654
-- title:
--   OAI.SphericalPerceptronFreeEnergy.indexedDepthLaw_finiteGG: intermediate lemma from OpenAI, Spherical perceptron free energy (OpenAI result family 222)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SphericalPerceptronFreeEnergy.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Spherical perceptron free energy (OpenAI result family 222)*, OpenAI Math Release, September 24, 2026, result family 222, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SphericalPerceptronFreeEnergy.indexedDepthLaw_finiteGG` of [lean/OAI/Probability/Perceptron/Variational/DepthGG.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/Perceptron/Variational/DepthGG.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SphericalPerceptronFreeEnergy`, with `open MeasureTheory ProbabilityTheory Set Filter`, `open scoped Classical ENNReal NNReal BigOperators Topology`):
--
--   ```lean
--   theorem indexedDepthLaw_finiteGG (k : ℕ) (z : Fin k → ℝ)
--       (hz : StrictMono z) (hz0 : ∀ i, 0 < z i) (hz1 : ∀ i, z i < 1) :
--       FiniteGG (indexedDepthLaw k z : Measure (FiniteOverlap (Fin (k+1))))
--   ```
--
--   **Definitions.** The statement is written with `OAI.SphericalPerceptronFreeEnergy.FiniteGG`, `OAI.SphericalPerceptronFreeEnergy.FiniteOverlap` and `OAI.SphericalPerceptronFreeEnergy.indexedDepthLaw` (definitions bundle `OAIQ61Pf000` of this split).
--
--   **Used by.** The proof of `OAI.SphericalPerceptronFreeEnergy.bulk_cavity_data` of this split imports it.
-- source:
--   OpenAI, Spherical perceptron free energy (OpenAI result family 222), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 222; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/PerceptronFreeEnergy.lean; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/Perceptron/Variational/DepthGG.lean (declaration OAI.SphericalPerceptronFreeEnergy.indexedDepthLaw_finiteGG)

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

theorem indexedDepthLaw_finiteGG (k : ℕ) (z : Fin k → ℝ)
    (hz : StrictMono z) (hz0 : ∀ i, 0 < z i) (hz1 : ∀ i, z i < 1) :
    FiniteGG (indexedDepthLaw k z : Measure (FiniteOverlap (Fin (k+1)))) := by
  sorry

end SphericalPerceptronFreeEnergy

end

end OAI
end
