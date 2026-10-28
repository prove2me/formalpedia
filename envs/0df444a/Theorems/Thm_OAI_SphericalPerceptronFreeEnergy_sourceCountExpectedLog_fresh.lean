-- Prove2me | Theorems.Thm_OAI_SphericalPerceptronFreeEnergy_sourceCountExpectedLog_fresh
-- name    : OAI.SphericalPerceptronFreeEnergy.sourceCountExpectedLog_fresh
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T22:12:09.806716+00:00
-- url     : https://prove2.me/theorems/72e1b157-9017-4797-9e1f-ea7eebcf350e
-- title:
--   OAI.SphericalPerceptronFreeEnergy.sourceCountExpectedLog_fresh: intermediate lemma from OpenAI, Spherical perceptron free energy (OpenAI result family 222)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SphericalPerceptronFreeEnergy.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Spherical perceptron free energy (OpenAI result family 222)*, OpenAI Math Release, September 24, 2026, result family 222, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SphericalPerceptronFreeEnergy.sourceCountExpectedLog_fresh` of [lean/OAI/Probability/Perceptron/Variational/FixedCount.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/Perceptron/Variational/FixedCount.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SphericalPerceptronFreeEnergy`, with `open MeasureTheory ProbabilityTheory Filter Set`, `open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction`):
--
--   ```lean
--   lemma sourceCountExpectedLog_fresh (n M k : ℕ) (f : ℝ →ᵇℝ) (p d : Fin (n+1)→ℕ)
--       (h : Fin (k+1)→ℝ) (hh0 : ∀ i, 0≤h i) (hh : Monotone h)
--       (u : Fin (n+1)→ℝ) (z : Fin k→ℝ)
--       (hz : StrictMono z) (hz0 : ∀ i, 0<z i) (hz1 : ∀ i, z i<1) :
--       sourceCountExpectedLog n k f p d h z u (M+1)-sourceCountExpectedLog n k f p d h z u M=
--         ∫ a, ∫ g, Real.log (freshThermalPartition (sourceCountKernel n k)
--           (sourceCountHamiltonian n M k f p d h u) (fun x => x.1.val) f (a,g))
--           ∂stdGaussian (EuclideanSpace ℝ (Fin (n+1))) ∂sourceCountLaw n k z
--   ```
--
--   **Definitions.** The statement is written with `OAI.SphericalPerceptronFreeEnergy.IndexedCascadeBase`, `OAI.SphericalPerceptronFreeEnergy.IndexedLeaf`, `OAI.SphericalPerceptronFreeEnergy.NormalizedSpin`, `OAI.SphericalPerceptronFreeEnergy.SourceCountData`, `OAI.SphericalPerceptronFreeEnergy.freshThermalPartition`, `OAI.SphericalPerceptronFreeEnergy.sourceCountKernel` and `OAI.SphericalPerceptronFreeEnergy.sourceCountLaw` (definitions bundle `OAIQ61Pf000` of this split); `OAI.SphericalPerceptronFreeEnergy.sourceCountExpectedLog` and `OAI.SphericalPerceptronFreeEnergy.sourceCountHamiltonian` (definitions bundle `OAIQ61Pf002` of this split); `OAI.SphericalPerceptronFreeEnergy.Spin` (the published bundle `Def_PerceptronFreeEnergy`).
--
--   **Used by.** The proof of `OAI.SphericalPerceptronFreeEnergy.main` of this split imports it.
-- source:
--   OpenAI, Spherical perceptron free energy (OpenAI result family 222), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 222; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/PerceptronFreeEnergy.lean; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/Perceptron/Variational/FixedCount.lean (declaration OAI.SphericalPerceptronFreeEnergy.sourceCountExpectedLog_fresh)

import Mathlib
import Definitions.Def_PerceptronFreeEnergy
import Definitions.Def_OAIQ61Pf002

section

attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.bulkFiniteReplicaLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.bulkSpinKernel_markov _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.indexedInfiniteLeafMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelProdCarrierIndexedCascadeBaseIndexedCascadeMarksIndexedLeafIndexedTerminalBaseKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw _root_.OAI.SphericalPerceptronFreeEnergy.unitSphereAmbientLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

lemma sourceCountExpectedLog_fresh (n M k : ℕ) (f : ℝ →ᵇℝ) (p d : Fin (n+1)→ℕ)
    (h : Fin (k+1)→ℝ) (hh0 : ∀ i, 0≤h i) (hh : Monotone h)
    (u : Fin (n+1)→ℝ) (z : Fin k→ℝ)
    (hz : StrictMono z) (hz0 : ∀ i, 0<z i) (hz1 : ∀ i, z i<1) :
    sourceCountExpectedLog n k f p d h z u (M+1)-sourceCountExpectedLog n k f p d h z u M=
      ∫ a, ∫ g, Real.log (freshThermalPartition (sourceCountKernel n k)
        (sourceCountHamiltonian n M k f p d h u) (fun x => x.1.val) f (a,g))
        ∂stdGaussian (EuclideanSpace ℝ (Fin (n+1))) ∂sourceCountLaw n k z := by
  sorry

end SphericalPerceptronFreeEnergy
end

end OAI
end
