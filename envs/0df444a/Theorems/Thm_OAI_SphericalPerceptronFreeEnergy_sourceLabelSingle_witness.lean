-- Prove2me | Theorems.Thm_OAI_SphericalPerceptronFreeEnergy_sourceLabelSingle_witness
-- name    : OAI.SphericalPerceptronFreeEnergy.sourceLabelSingle_witness
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T22:16:29.134962+00:00
-- url     : https://prove2.me/theorems/bebe2fd2-baa5-481f-9f7a-a5825bade500
-- title:
--   OAI.SphericalPerceptronFreeEnergy.sourceLabelSingle_witness: intermediate lemma from OpenAI, Spherical perceptron free energy (OpenAI result family 222)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SphericalPerceptronFreeEnergy.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Spherical perceptron free energy (OpenAI result family 222)*, OpenAI Math Release, September 24, 2026, result family 222, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SphericalPerceptronFreeEnergy.sourceLabelSingle_witness` of [lean/OAI/Probability/Perceptron/Variational/LabelSingleRestoredValue.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/Perceptron/Variational/LabelSingleRestoredValue.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SphericalPerceptronFreeEnergy`, with `open MeasureTheory ProbabilityTheory Set Filter`, `open scoped NNReal ENNReal BigOperators BoundedContinuousFunction Topology`):
--
--   ```lean
--   lemma sourceLabelSingle_witness (k : ℕ) (q : Fin (k+1)→Time) (hq : Monotone q)
--       (f : ℝ →ᵇ ℝ) (g : Jet3) (v w : ℝ →ᵇ ℝ)
--       (p e : (n : ℕ)→Fin (n+1)→ℕ) (h : ℕ→Fin (k+1)→ℝ)
--       (hh0 : ∀ n i,0≤h n i) (hh : ∀ n,Monotone (h n)) (u : (n : ℕ)→Fin (n+1)→ℝ)
--       (z : Fin k→ℝ) (hz : StrictMono z) (hz0 : ∀ i,0<z i) (hz1 : ∀ i,z i<1)
--       (t : ℕ→ℝ≥0) (s : ℕ→ℕ) {ν : ProbabilityMeasure (CompactArray CompactJointOverlap)}
--       (hlim : Tendsto (fun n => sourceGibbsArrayLaw (s n) k f (p (s n)) (e (s n)) (h (s n))
--         (u (s n)) z (t (s n))) atTop (𝓝 ν)) :
--       ∃ η : ProbabilityMeasure (WeightedRestorationRange g.f (singleRestorationBound g.f v w)),
--         (∀ j, (∫ x, x.1.val*x.2.val^j ∂(η : Measure (WeightedRestorationRange g.f (singleRestorationBound g.f v w))))=
--           ∫ Q, labelRestorationBlockMoment (fun i => (q i:ℝ)) g.f (fun _ : Fin 1 => v) (fun _ => w)
--             1 j (compactBlock (1+j) Q) ∂ν) ∧
--         (∫ x, x.1.val*restorationReciprocal g.f 1 x.2 ∂(η : Measure (WeightedRestorationRange g.f (singleRestorationBound g.f v w))))=
--           labelSingleCoefficient k z (fun i => (q i:ℝ)) g (⟨1-q (Fin.last k),sub_nonneg.mpr (q (Fin.last k)).prop.2⟩ : ℝ≥0) v *
--           labelSingleCoefficient k z (fun i => (q i:ℝ)) g (⟨1-q (Fin.last k),sub_nonneg.mpr (q (Fin.last k)).prop.2⟩ : ℝ≥0) w
--   ```
--
--   **Definitions.** The statement is written with `OAI.SphericalPerceptronFreeEnergy.CompactArray`, `OAI.SphericalPerceptronFreeEnergy.CompactBlock`, `OAI.SphericalPerceptronFreeEnergy.CompactJointOverlap`, `OAI.SphericalPerceptronFreeEnergy.CompactOverlap`, `OAI.SphericalPerceptronFreeEnergy.Jet3`, `OAI.SphericalPerceptronFreeEnergy.RestorationRange`, `OAI.SphericalPerceptronFreeEnergy.WeightedRestorationRange`, `OAI.SphericalPerceptronFreeEnergy.compactBlock`, `OAI.SphericalPerceptronFreeEnergy.labelRestorationBlockMoment` and `OAI.SphericalPerceptronFreeEnergy.labelSingleCoefficient` (definitions bundle `OAIQ61Pf000` of this split); `OAI.SphericalPerceptronFreeEnergy.restorationReciprocal`, `OAI.SphericalPerceptronFreeEnergy.singleRestorationBound` and `OAI.SphericalPerceptronFreeEnergy.sourceGibbsArrayLaw` (definitions bundle `OAIQ61Pf002` of this split); `OAI.SphericalPerceptronFreeEnergy.Time` (the published bundle `Def_PerceptronFreeEnergy`).
--
--   **Used by.** The proof of `OAI.SphericalPerceptronFreeEnergy.bulk_single_limit_exists` of this split imports it.
-- source:
--   OpenAI, Spherical perceptron free energy (OpenAI result family 222), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 222; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/PerceptronFreeEnergy.lean; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/Perceptron/Variational/LabelSingleRestoredValue.lean (declaration OAI.SphericalPerceptronFreeEnergy.sourceLabelSingle_witness)

import Mathlib
import Definitions.Def_PerceptronFreeEnergy
import Definitions.Def_OAIQ61Pf002

section

attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_fst_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.indexedInfiniteLeafMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.instCoeFunBoundedFieldForallElemRealTime _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureSourceCountDataSourceCountLaw _root_.OAI.SphericalPerceptronFreeEnergy.markedTimePair_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal BigOperators BoundedContinuousFunction Topology

lemma sourceLabelSingle_witness (k : ℕ) (q : Fin (k+1)→Time) (hq : Monotone q)
    (f : ℝ →ᵇ ℝ) (g : Jet3) (v w : ℝ →ᵇ ℝ)
    (p e : (n : ℕ)→Fin (n+1)→ℕ) (h : ℕ→Fin (k+1)→ℝ)
    (hh0 : ∀ n i,0≤h n i) (hh : ∀ n,Monotone (h n)) (u : (n : ℕ)→Fin (n+1)→ℝ)
    (z : Fin k→ℝ) (hz : StrictMono z) (hz0 : ∀ i,0<z i) (hz1 : ∀ i,z i<1)
    (t : ℕ→ℝ≥0) (s : ℕ→ℕ) {ν : ProbabilityMeasure (CompactArray CompactJointOverlap)}
    (hlim : Tendsto (fun n => sourceGibbsArrayLaw (s n) k f (p (s n)) (e (s n)) (h (s n))
      (u (s n)) z (t (s n))) atTop (𝓝 ν)) :
    ∃ η : ProbabilityMeasure (WeightedRestorationRange g.f (singleRestorationBound g.f v w)),
      (∀ j, (∫ x, x.1.val*x.2.val^j ∂(η : Measure (WeightedRestorationRange g.f (singleRestorationBound g.f v w))))=
        ∫ Q, labelRestorationBlockMoment (fun i => (q i:ℝ)) g.f (fun _ : Fin 1 => v) (fun _ => w)
          1 j (compactBlock (1+j) Q) ∂ν) ∧
      (∫ x, x.1.val*restorationReciprocal g.f 1 x.2 ∂(η : Measure (WeightedRestorationRange g.f (singleRestorationBound g.f v w))))=
        labelSingleCoefficient k z (fun i => (q i:ℝ)) g (⟨1-q (Fin.last k),sub_nonneg.mpr (q (Fin.last k)).prop.2⟩ : ℝ≥0) v *
        labelSingleCoefficient k z (fun i => (q i:ℝ)) g (⟨1-q (Fin.last k),sub_nonneg.mpr (q (Fin.last k)).prop.2⟩ : ℝ≥0) w := by
  sorry

end SphericalPerceptronFreeEnergy
end

end OAI
end
