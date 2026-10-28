-- Prove2me | Theorems.Thm_OAI_SphericalPerceptronFreeEnergy_cavityLabel_full_evaluation
-- name    : OAI.SphericalPerceptronFreeEnergy.cavityLabel_full_evaluation
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T22:05:06.583048+00:00
-- url     : https://prove2.me/theorems/edf9b97a-0676-4848-b8f9-10c2ef87d32c
-- title:
--   OAI.SphericalPerceptronFreeEnergy.cavityLabel_full_evaluation: intermediate lemma from OpenAI, Spherical perceptron free energy (OpenAI result family 222)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SphericalPerceptronFreeEnergy.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Spherical perceptron free energy (OpenAI result family 222)*, OpenAI Math Release, September 24, 2026, result family 222, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SphericalPerceptronFreeEnergy.cavityLabel_full_evaluation` of [lean/OAI/Probability/Perceptron/Cavity/CavityFullEvaluation.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/Perceptron/Cavity/CavityFullEvaluation.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SphericalPerceptronFreeEnergy`, with `open MeasureTheory ProbabilityTheory Set`, `open scoped Topology BigOperators BoundedContinuousFunction NNReal`):
--
--   ```lean
--   theorem cavityLabel_full_evaluation (n d : ℕ) {K : ℝ} {k : ℕ}
--       (p : Fin (k+1)→BulkPairRange K) (D : BulkPairRange K)
--       (hp0 : ∀ i,0 ≤ cavityPairProfile n d p 0 i)
--       (hpm : ∀ i,Monotone (fun l=>cavityPairProfile n d p l i))
--       (hpD : ∀ i,cavityPairProfile n d p (Fin.last k) i ≤ cavityPairDiagonal n d D i)
--       (f : ℝ→ᵇℝ) (z : Fin k→ℝ) (hz : StrictMono z) (hz0 : ∀ i,0<z i) (hz1 : ∀ i,z i<1)
--       (a s : ℝ≥0) (ha : (a:ℝ)=D.2.val-(p (Fin.last k)).2.val)
--       (hs : (s:ℝ)=D.1.val-(p (Fin.last k)).1.val) :
--       let q:=cavityPairProfile n d p
--       let σ:=fun i=>Real.sqrt (cavityPairDiagonal n d D i-q (Fin.last k) i)
--       (∫ t,Real.log (cavityLabelFullPartition n d k f σ q t)
--         ∂(indexedCascadeBaseLaw k z : Measure (IndexedCascadeBase k)).prod countableGaussianLaw)=
--       (n+1:ℕ)*a/2+∫ b,finiteCascadeLogRecursion (cavityRPCMarkLaw n d)
--         (cavityRPCStep n d (stepFieldIncrement k (fun l=>(p l).2.val/2))
--           (fun j=>profileGaussianStep (fun l (_ : Fin 1)=>(p l).1.val) j 0)) k z
--         (cavityRPCTerminal n d (heatLogBCF s 1 f))
--         (cavityRPCRootState n d (Real.sqrt (p 0).2.val) (Real.sqrt (p 0).1.val) b)
--         ∂(cavityRPCMarkLaw n d : Measure (CavityRPCMark n d))
--   ```
--
--   **Definitions.** The statement is written with `OAI.SphericalPerceptronFreeEnergy.BulkPairRange`, `OAI.SphericalPerceptronFreeEnergy.CavityRPCMark`, `OAI.SphericalPerceptronFreeEnergy.CavityRPCState`, `OAI.SphericalPerceptronFreeEnergy.CompactOverlap`, `OAI.SphericalPerceptronFreeEnergy.IndexedCascadeBase`, `OAI.SphericalPerceptronFreeEnergy.cavityLabelFullPartition`, `OAI.SphericalPerceptronFreeEnergy.cavityPairDiagonal`, `OAI.SphericalPerceptronFreeEnergy.cavityPairProfile`, `OAI.SphericalPerceptronFreeEnergy.cavityRPCMarkLaw`, `OAI.SphericalPerceptronFreeEnergy.cavityRPCRootState`, `OAI.SphericalPerceptronFreeEnergy.cavityRPCStep`, `OAI.SphericalPerceptronFreeEnergy.cavityRPCTerminal`, `OAI.SphericalPerceptronFreeEnergy.countableGaussianLaw`, `OAI.SphericalPerceptronFreeEnergy.finiteCascadeLogRecursion`, `OAI.SphericalPerceptronFreeEnergy.heatLogBCF`, `OAI.SphericalPerceptronFreeEnergy.indexedCascadeBaseLaw`, `OAI.SphericalPerceptronFreeEnergy.profileGaussianStep` and `OAI.SphericalPerceptronFreeEnergy.stepFieldIncrement` (definitions bundle `OAIQ61Pf000` of this split).
--
--   **Used by.** The proof of `OAI.SphericalPerceptronFreeEnergy.cavityLabel_full_value` of this split imports it.
-- source:
--   OpenAI, Spherical perceptron free energy (OpenAI result family 222), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 222; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/PerceptronFreeEnergy.lean; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/Perceptron/Cavity/CavityFullEvaluation.lean (declaration OAI.SphericalPerceptronFreeEnergy.cavityLabel_full_evaluation)

import Mathlib
import Definitions.Def_OAIQ61Pf000

section

attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.indexedInfiniteLeafMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureSourceCountDataSourceCountLaw _root_.OAI.SphericalPerceptronFreeEnergy.markedTimePair_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Set
open scoped Topology BigOperators BoundedContinuousFunction NNReal

theorem cavityLabel_full_evaluation (n d : ℕ) {K : ℝ} {k : ℕ}
    (p : Fin (k+1)→BulkPairRange K) (D : BulkPairRange K)
    (hp0 : ∀ i,0 ≤ cavityPairProfile n d p 0 i)
    (hpm : ∀ i,Monotone (fun l=>cavityPairProfile n d p l i))
    (hpD : ∀ i,cavityPairProfile n d p (Fin.last k) i ≤ cavityPairDiagonal n d D i)
    (f : ℝ→ᵇℝ) (z : Fin k→ℝ) (hz : StrictMono z) (hz0 : ∀ i,0<z i) (hz1 : ∀ i,z i<1)
    (a s : ℝ≥0) (ha : (a:ℝ)=D.2.val-(p (Fin.last k)).2.val)
    (hs : (s:ℝ)=D.1.val-(p (Fin.last k)).1.val) :
    let q:=cavityPairProfile n d p
    let σ:=fun i=>Real.sqrt (cavityPairDiagonal n d D i-q (Fin.last k) i)
    (∫ t,Real.log (cavityLabelFullPartition n d k f σ q t)
      ∂(indexedCascadeBaseLaw k z : Measure (IndexedCascadeBase k)).prod countableGaussianLaw)=
    (n+1:ℕ)*a/2+∫ b,finiteCascadeLogRecursion (cavityRPCMarkLaw n d)
      (cavityRPCStep n d (stepFieldIncrement k (fun l=>(p l).2.val/2))
        (fun j=>profileGaussianStep (fun l (_ : Fin 1)=>(p l).1.val) j 0)) k z
      (cavityRPCTerminal n d (heatLogBCF s 1 f))
      (cavityRPCRootState n d (Real.sqrt (p 0).2.val) (Real.sqrt (p 0).1.val) b)
      ∂(cavityRPCMarkLaw n d : Measure (CavityRPCMark n d)) := by
  sorry

end SphericalPerceptronFreeEnergy
end

end OAI
end
