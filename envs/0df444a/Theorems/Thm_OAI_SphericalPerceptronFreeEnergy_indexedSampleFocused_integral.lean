-- Prove2me | Theorems.Thm_OAI_SphericalPerceptronFreeEnergy_indexedSampleFocused_integral
-- name    : OAI.SphericalPerceptronFreeEnergy.indexedSampleFocused_integral
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T22:07:29.926246+00:00
-- url     : https://prove2.me/theorems/3d710ff7-fa27-4028-9115-711004d453e3
-- title:
--   OAI.SphericalPerceptronFreeEnergy.indexedSampleFocused_integral: intermediate lemma from OpenAI, Spherical perceptron free energy (OpenAI result family 222)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SphericalPerceptronFreeEnergy.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Spherical perceptron free energy (OpenAI result family 222)*, OpenAI Math Release, September 24, 2026, result family 222, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SphericalPerceptronFreeEnergy.indexedSampleFocused_integral` of [lean/OAI/Probability/Perceptron/Variational/FocusedSampleLaw.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/Perceptron/Variational/FocusedSampleLaw.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SphericalPerceptronFreeEnergy`, with `open MeasureTheory ProbabilityTheory Set Filter`, `open scoped Classical ENNReal NNReal BigOperators Topology`):
--
--   ```lean
--   theorem indexedSampleFocused_integral (n : ℕ) (z : Fin n → ℝ) (hz : StrictMono z)
--       (hz0 : ∀ i, 0 < z i) (hz1 : ∀ i, z i < 1)
--       (d : ℕ) (hd : d ≤ n) (s : CascadeVisitShape n) (hs : s.Valid n) :
--       (∫⁻ b, indexedSampleFocused n d s hs b ∂indexedCascadeBaseLaw n z) =
--         cascadeShapeLikelihood n z 0 s *
--           ENNReal.ofReal (focusedShapeNumerator n z 0 d s/(cascadeVisitCount n s:ℝ))
--   ```
--
--   **Definitions.** The statement is written with `OAI.SphericalPerceptronFreeEnergy.CascadeVisitShape`, `OAI.SphericalPerceptronFreeEnergy.IndexedCascadeBase`, `OAI.SphericalPerceptronFreeEnergy.cascadeShapeLikelihood`, `OAI.SphericalPerceptronFreeEnergy.cascadeVisitCount`, `OAI.SphericalPerceptronFreeEnergy.focusedShapeNumerator`, `OAI.SphericalPerceptronFreeEnergy.indexedCascadeBaseLaw`, `OAI.SphericalPerceptronFreeEnergy.indexedSampleFocused` and `OAI.SphericalPerceptronFreeEnergy.CascadeVisitShape.Valid` (definitions bundle `OAIQ61Pf000` of this split).
--
--   **Used by.** The proofs of `OAI.SphericalPerceptronFreeEnergy.indexedDepthLaw_finiteGG` and `OAI.SphericalPerceptronFreeEnergy.indexedDepthLaw_pair_weights` of this split import it.
-- source:
--   OpenAI, Spherical perceptron free energy (OpenAI result family 222), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 222; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/PerceptronFreeEnergy.lean; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/Perceptron/Variational/FocusedSampleLaw.lean (declaration OAI.SphericalPerceptronFreeEnergy.indexedSampleFocused_integral)

import Mathlib
import Definitions.Def_OAIQ61Pf000

section

attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelProdCarrierIndexedCascadeBaseIndexedCascadeMarksIndexedLeafIndexedTerminalBaseKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureSourceCountDataSourceCountLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical ENNReal NNReal BigOperators Topology

theorem indexedSampleFocused_integral (n : ℕ) (z : Fin n → ℝ) (hz : StrictMono z)
    (hz0 : ∀ i, 0 < z i) (hz1 : ∀ i, z i < 1)
    (d : ℕ) (hd : d ≤ n) (s : CascadeVisitShape n) (hs : s.Valid n) :
    (∫⁻ b, indexedSampleFocused n d s hs b ∂indexedCascadeBaseLaw n z) =
      cascadeShapeLikelihood n z 0 s *
        ENNReal.ofReal (focusedShapeNumerator n z 0 d s/(cascadeVisitCount n s:ℝ)) := by
  sorry

end SphericalPerceptronFreeEnergy
end

end OAI
end
