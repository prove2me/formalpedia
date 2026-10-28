-- Prove2me | Theorems.Thm_OAI_SphericalPerceptronFreeEnergy_sourceLabelRestorationRatio_pair_value
-- name    : OAI.SphericalPerceptronFreeEnergy.sourceLabelRestorationRatio_pair_value
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T22:13:44.385035+00:00
-- url     : https://prove2.me/theorems/3be5051c-e764-4052-a1c2-0c6270e83e75
-- title:
--   OAI.SphericalPerceptronFreeEnergy.sourceLabelRestorationRatio_pair_value: intermediate lemma from OpenAI, Spherical perceptron free energy (OpenAI result family 222)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SphericalPerceptronFreeEnergy.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Spherical perceptron free energy (OpenAI result family 222)*, OpenAI Math Release, September 24, 2026, result family 222, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SphericalPerceptronFreeEnergy.sourceLabelRestorationRatio_pair_value` of [lean/OAI/Probability/Perceptron/Variational/LabelPairTestValue.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/Perceptron/Variational/LabelPairTestValue.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SphericalPerceptronFreeEnergy`, with `open MeasureTheory ProbabilityTheory Set Filter`, `open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction`):
--
--   ```lean
--   lemma sourceLabelRestorationRatio_pair_value (n k : ℕ) (f : ℝ →ᵇ ℝ) (g : Jet3)
--       (p e : Fin (n+1)→ℕ) (h : Fin (k+1)→ℝ) (hh0 : ∀ i,0≤h i) (hh : Monotone h)
--       (u : Fin (n+1)→ℝ) (q : Fin (k+1)→Time) (s : ℝ≥0) (v w : ℝ →ᵇ ℝ)
--       (F : CompactOverlap →ᵇ ℝ) (z : Fin k→ℝ)
--       (hz : StrictMono z) (hz0 : ∀ i,0<z i) (hz1 : ∀ i,z i<1) (t : ℝ≥0) :
--       sourceLabelRestorationRatio n k 2 (fun i => (q i:ℝ)) s f g.f (fun _ => v) (fun _ => w)
--         (labelProfilePairTest q F) p e h u z t =
--         ∑ d, F (timeSpin (q d))*(twoVisitMass k z d).toReal*
--           (labelPairCoefficient k z (fun i => (q i:ℝ)) g s v d *
--             labelPairCoefficient k z (fun i => (q i:ℝ)) g s w d)
--   ```
--
--   **Definitions.** The statement is written with `OAI.SphericalPerceptronFreeEnergy.CompactOverlap`, `OAI.SphericalPerceptronFreeEnergy.Jet3`, `OAI.SphericalPerceptronFreeEnergy.labelPairCoefficient` and `OAI.SphericalPerceptronFreeEnergy.labelProfilePairTest` (definitions bundle `OAIQ61Pf000` of this split); `OAI.SphericalPerceptronFreeEnergy.sourceLabelRestorationRatio`, `OAI.SphericalPerceptronFreeEnergy.timeSpin` and `OAI.SphericalPerceptronFreeEnergy.twoVisitMass` (definitions bundle `OAIQ61Pf002` of this split); `OAI.SphericalPerceptronFreeEnergy.Time` (the published bundle `Def_PerceptronFreeEnergy`).
--
--   **Used by.** The proofs of `OAI.SphericalPerceptronFreeEnergy.quantile_marked_pair_reference_exists` and `OAI.SphericalPerceptronFreeEnergy.quantile_pair_reference_exists` of this split import it.
-- source:
--   OpenAI, Spherical perceptron free energy (OpenAI result family 222), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 222; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/PerceptronFreeEnergy.lean; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/Perceptron/Variational/LabelPairTestValue.lean (declaration OAI.SphericalPerceptronFreeEnergy.sourceLabelRestorationRatio_pair_value)

import Mathlib
import Definitions.Def_PerceptronFreeEnergy
import Definitions.Def_OAIQ61Pf002

section

attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.bulkFiniteReplicaLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_fst_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.indexedInfiniteLeafMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.instCoeFunBoundedFieldForallElemRealTime _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureSourceCountDataSourceCountLaw _root_.OAI.SphericalPerceptronFreeEnergy.markedTimePair_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction

lemma sourceLabelRestorationRatio_pair_value (n k : ℕ) (f : ℝ →ᵇ ℝ) (g : Jet3)
    (p e : Fin (n+1)→ℕ) (h : Fin (k+1)→ℝ) (hh0 : ∀ i,0≤h i) (hh : Monotone h)
    (u : Fin (n+1)→ℝ) (q : Fin (k+1)→Time) (s : ℝ≥0) (v w : ℝ →ᵇ ℝ)
    (F : CompactOverlap →ᵇ ℝ) (z : Fin k→ℝ)
    (hz : StrictMono z) (hz0 : ∀ i,0<z i) (hz1 : ∀ i,z i<1) (t : ℝ≥0) :
    sourceLabelRestorationRatio n k 2 (fun i => (q i:ℝ)) s f g.f (fun _ => v) (fun _ => w)
      (labelProfilePairTest q F) p e h u z t =
      ∑ d, F (timeSpin (q d))*(twoVisitMass k z d).toReal*
        (labelPairCoefficient k z (fun i => (q i:ℝ)) g s v d *
          labelPairCoefficient k z (fun i => (q i:ℝ)) g s w d) := by
  sorry

end SphericalPerceptronFreeEnergy
end

end OAI
end
