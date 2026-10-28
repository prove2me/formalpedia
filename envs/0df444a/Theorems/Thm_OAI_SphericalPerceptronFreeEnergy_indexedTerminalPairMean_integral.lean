-- Prove2me | Theorems.Thm_OAI_SphericalPerceptronFreeEnergy_indexedTerminalPairMean_integral
-- name    : OAI.SphericalPerceptronFreeEnergy.indexedTerminalPairMean_integral
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T22:10:54.815401+00:00
-- url     : https://prove2.me/theorems/6a3aec76-c657-408d-9a17-02825cce22ba
-- title:
--   OAI.SphericalPerceptronFreeEnergy.indexedTerminalPairMean_integral: intermediate lemma from OpenAI, Spherical perceptron free energy (OpenAI result family 222)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SphericalPerceptronFreeEnergy.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Spherical perceptron free energy (OpenAI result family 222)*, OpenAI Math Release, September 24, 2026, result family 222, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SphericalPerceptronFreeEnergy.indexedTerminalPairMean_integral` of [lean/OAI/Probability/Perceptron/Pressure/IndexedTerminalProduct.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/Perceptron/Pressure/IndexedTerminalProduct.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SphericalPerceptronFreeEnergy`, with `open MeasureTheory ProbabilityTheory Set`, `open scoped ENNReal NNReal BigOperators`):
--
--   ```lean
--   lemma indexedTerminalPairMean_integral [Nonempty S] (ν : ProbabilityMeasure S) (step : X×S→X)
--       (hs : Measurable step) (n : ℕ) (z : Fin n→ℝ) (hz : StrictMono z)
--       (hz0 : ∀ i, 0<z i) (hz1 : ∀ i, z i<1) (H : X→ℝ) (hH : Measurable H)
--       (hI : finiteCascadeFractionalIntegrable ν step H n z) (x : X) (d : Fin (n+1))
--       (f : X→ℝ) (hf : Measurable f) (C : ℝ) (hC : 0≤C) (hfB : ∀ y, |f y|≤C) :
--       (∫ p, indexedTerminalPairMean step n H x d f p
--         ∂(indexedCascadeBaseLaw n z : Measure (IndexedCascadeBase n)).prod
--           (indexedCascadeMarksLaw ν n : Measure (IndexedCascadeMarks S n))) =
--         (twoVisitMass n z d).toReal * pathCorrelation n
--           (fun i => tiltedStateStep ν step (z i) (finiteCascadeShifts ν step n z H i)) f d x
--   ```
--
--   **Definitions.** The statement is written with `OAI.SphericalPerceptronFreeEnergy.IndexedCascadeBase`, `OAI.SphericalPerceptronFreeEnergy.IndexedCascadeMarks`, `OAI.SphericalPerceptronFreeEnergy.finiteCascadeFractionalIntegrable`, `OAI.SphericalPerceptronFreeEnergy.finiteCascadeShifts`, `OAI.SphericalPerceptronFreeEnergy.indexedCascadeBaseLaw`, `OAI.SphericalPerceptronFreeEnergy.indexedCascadeMarksLaw`, `OAI.SphericalPerceptronFreeEnergy.indexedTerminalPairMean`, `OAI.SphericalPerceptronFreeEnergy.pathCorrelation` and `OAI.SphericalPerceptronFreeEnergy.tiltedStateStep` (definitions bundle `OAIQ61Pf000` of this split); `OAI.SphericalPerceptronFreeEnergy.twoVisitMass` (definitions bundle `OAIQ61Pf002` of this split).
--
--   **Used by.** The proof of `OAI.SphericalPerceptronFreeEnergy.sourceLabelRestorationRatio_pair_value` of this split imports it.
-- source:
--   OpenAI, Spherical perceptron free energy (OpenAI result family 222), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 222; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/PerceptronFreeEnergy.lean; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/Perceptron/Pressure/IndexedTerminalProduct.lean (declaration OAI.SphericalPerceptronFreeEnergy.indexedTerminalPairMean_integral)

import Mathlib
import Definitions.Def_OAIQ61Pf002

section

attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.indexedInfiniteLeafMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureSourceCountDataSourceCountLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators
namespace SphericalPerceptronFreeEnergy
variable {X Y S T : Type} [MeasurableSpace X] [MeasurableSpace Y]
  [MeasurableSpace S] [MeasurableSpace T]

lemma indexedTerminalPairMean_integral [Nonempty S] (ν : ProbabilityMeasure S) (step : X×S→X)
    (hs : Measurable step) (n : ℕ) (z : Fin n→ℝ) (hz : StrictMono z)
    (hz0 : ∀ i, 0<z i) (hz1 : ∀ i, z i<1) (H : X→ℝ) (hH : Measurable H)
    (hI : finiteCascadeFractionalIntegrable ν step H n z) (x : X) (d : Fin (n+1))
    (f : X→ℝ) (hf : Measurable f) (C : ℝ) (hC : 0≤C) (hfB : ∀ y, |f y|≤C) :
    (∫ p, indexedTerminalPairMean step n H x d f p
      ∂(indexedCascadeBaseLaw n z : Measure (IndexedCascadeBase n)).prod
        (indexedCascadeMarksLaw ν n : Measure (IndexedCascadeMarks S n))) =
      (twoVisitMass n z d).toReal * pathCorrelation n
        (fun i => tiltedStateStep ν step (z i) (finiteCascadeShifts ν step n z H i)) f d x := by
  sorry

end SphericalPerceptronFreeEnergy
end

end OAI
end
