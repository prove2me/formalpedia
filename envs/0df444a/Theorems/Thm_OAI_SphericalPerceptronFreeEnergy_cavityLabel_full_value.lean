-- Prove2me | Theorems.Thm_OAI_SphericalPerceptronFreeEnergy_cavityLabel_full_value
-- name    : OAI.SphericalPerceptronFreeEnergy.cavityLabel_full_value
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T22:04:37.188967+00:00
-- url     : https://prove2.me/theorems/4e8191bf-79e4-4a27-8664-bc1433f88949
-- title:
--   OAI.SphericalPerceptronFreeEnergy.cavityLabel_full_value: intermediate lemma from OpenAI, Spherical perceptron free energy (OpenAI result family 222)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SphericalPerceptronFreeEnergy.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Spherical perceptron free energy (OpenAI result family 222)*, OpenAI Math Release, September 24, 2026, result family 222, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SphericalPerceptronFreeEnergy.cavityLabel_full_value` of [lean/OAI/Probability/Perceptron/Cavity/CavityFullEvaluation.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/Perceptron/Cavity/CavityFullEvaluation.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SphericalPerceptronFreeEnergy`, with `open MeasureTheory ProbabilityTheory Set`, `open scoped Topology BigOperators BoundedContinuousFunction NNReal`):
--
--   ```lean
--   theorem cavityLabel_full_value (n d : ℕ) {K : ℝ} {k : ℕ}
--       (p : Fin (k+1)→BulkPairRange K) (D : BulkPairRange K)
--       (hp0 : ∀ i,0 ≤ cavityPairProfile n d p 0 i)
--       (hpm : ∀ i,Monotone (fun l=>cavityPairProfile n d p l i))
--       (hpD : ∀ i,cavityPairProfile n d p (Fin.last k) i ≤ cavityPairDiagonal n d D i)
--       (q : Fin (k+1)→Time) (hpR : ∀ l,(p l).1.val=(q l:ℝ)) (hDR : D.1.val=1)
--       (w : Fin (k+1)→ℝ) (hw : ∀ l,0<w l) (hw1 : ∑ l,w l=1) (hq : Monotone q)
--       (g : Jet3) (P : Measure BrownianPath) [IsProbabilityMeasure P] (hB : IsBrownianReal brownianEval P) :
--       let Q:=cavityPairProfile n d p
--       let σ:=fun i=>Real.sqrt (cavityPairDiagonal n d D i-Q (Fin.last k) i)
--       (∫ t,Real.log (cavityLabelFullPartition n d k g.f σ Q t)
--         ∂(indexedCascadeBaseLaw k (stepCumulative w) : Measure (IndexedCascadeBase k)).prod countableGaussianLaw)=
--         (n+1:ℕ)*(D.2.val/2+finiteSphericalFieldValue n k w (fun l=>(p l).2.val/2))+
--           d*controlValue P g.f (weightedStepTrial w q (fun l=>(hw l).le) hw1)
--   ```
--
--   **Definitions.** The statement is written with `OAI.SphericalPerceptronFreeEnergy.BulkPairRange`, `OAI.SphericalPerceptronFreeEnergy.CompactOverlap`, `OAI.SphericalPerceptronFreeEnergy.IndexedCascadeBase`, `OAI.SphericalPerceptronFreeEnergy.Jet3`, `OAI.SphericalPerceptronFreeEnergy.cavityLabelFullPartition`, `OAI.SphericalPerceptronFreeEnergy.cavityPairDiagonal`, `OAI.SphericalPerceptronFreeEnergy.cavityPairProfile`, `OAI.SphericalPerceptronFreeEnergy.countableGaussianLaw`, `OAI.SphericalPerceptronFreeEnergy.finiteSphericalFieldValue`, `OAI.SphericalPerceptronFreeEnergy.indexedCascadeBaseLaw`, `OAI.SphericalPerceptronFreeEnergy.stepCumulative` and `OAI.SphericalPerceptronFreeEnergy.weightedStepTrial` (definitions bundle `OAIQ61Pf000` of this split); `OAI.SphericalPerceptronFreeEnergy.BrownianPath`, `OAI.SphericalPerceptronFreeEnergy.Time`, `OAI.SphericalPerceptronFreeEnergy.brownianEval`, `OAI.SphericalPerceptronFreeEnergy.controlValue` and `OAI.SphericalPerceptronFreeEnergy.instMeasurableSpaceBrownianPath` (the published bundle `Def_PerceptronFreeEnergy`).
--
--   **Used by.** The proof of `OAI.SphericalPerceptronFreeEnergy.roundedCavity_uncap` of this split imports it.
-- source:
--   OpenAI, Spherical perceptron free energy (OpenAI result family 222), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 222; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/PerceptronFreeEnergy.lean; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/Perceptron/Cavity/CavityFullEvaluation.lean (declaration OAI.SphericalPerceptronFreeEnergy.cavityLabel_full_value)

import Mathlib
import Definitions.Def_PerceptronFreeEnergy
import Definitions.Def_OAIQ61Pf000

section

attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.indexedInfiniteLeafMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureSourceCountDataSourceCountLaw _root_.OAI.SphericalPerceptronFreeEnergy.markedTimePair_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Set
open scoped Topology BigOperators BoundedContinuousFunction NNReal

theorem cavityLabel_full_value (n d : ℕ) {K : ℝ} {k : ℕ}
    (p : Fin (k+1)→BulkPairRange K) (D : BulkPairRange K)
    (hp0 : ∀ i,0 ≤ cavityPairProfile n d p 0 i)
    (hpm : ∀ i,Monotone (fun l=>cavityPairProfile n d p l i))
    (hpD : ∀ i,cavityPairProfile n d p (Fin.last k) i ≤ cavityPairDiagonal n d D i)
    (q : Fin (k+1)→Time) (hpR : ∀ l,(p l).1.val=(q l:ℝ)) (hDR : D.1.val=1)
    (w : Fin (k+1)→ℝ) (hw : ∀ l,0<w l) (hw1 : ∑ l,w l=1) (hq : Monotone q)
    (g : Jet3) (P : Measure BrownianPath) [IsProbabilityMeasure P] (hB : IsBrownianReal brownianEval P) :
    let Q:=cavityPairProfile n d p
    let σ:=fun i=>Real.sqrt (cavityPairDiagonal n d D i-Q (Fin.last k) i)
    (∫ t,Real.log (cavityLabelFullPartition n d k g.f σ Q t)
      ∂(indexedCascadeBaseLaw k (stepCumulative w) : Measure (IndexedCascadeBase k)).prod countableGaussianLaw)=
      (n+1:ℕ)*(D.2.val/2+finiteSphericalFieldValue n k w (fun l=>(p l).2.val/2))+
        d*controlValue P g.f (weightedStepTrial w q (fun l=>(hw l).le) hw1) := by
  sorry

end SphericalPerceptronFreeEnergy
end

end OAI
end
