-- Prove2me | Theorems.Thm_OAI_SphericalPerceptronFreeEnergy_compactGG_freshLog_control
-- name    : OAI.SphericalPerceptronFreeEnergy.compactGG_freshLog_control
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T22:08:36.430912+00:00
-- url     : https://prove2.me/theorems/d9f2fe51-0e8c-4b02-9e34-0e311b72592b
-- title:
--   OAI.SphericalPerceptronFreeEnergy.compactGG_freshLog_control: intermediate lemma from OpenAI, Spherical perceptron free energy (OpenAI result family 222)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SphericalPerceptronFreeEnergy.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Spherical perceptron free energy (OpenAI result family 222)*, OpenAI Math Release, September 24, 2026, result family 222, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SphericalPerceptronFreeEnergy.compactGG_freshLog_control` of [lean/OAI/Probability/Perceptron/Control/FreshControl.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/Perceptron/Control/FreshControl.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SphericalPerceptronFreeEnergy`, with `open MeasureTheory ProbabilityTheory Filter Set`, `open scoped Topology ENNReal NNReal BigOperators BoundedContinuousFunction`):
--
--   ```lean
--   theorem compactGG_freshLog_control (ν : ProbabilityMeasure (CompactArray CompactJointOverlap))
--       (hGG : ∀ (r : ℕ) (i : Fin r) (G : CompactBlock CompactJointOverlap r →ᵇ ℝ)
--         (a : CompactJointOverlap →ᵇ ℝ), compactGGDefect ν r i G a=0)
--       (hgeo : ∀ᵐ Q ∂(ν : Measure (CompactArray CompactJointOverlap)), CompactSpinGeometry Q)
--       (hn : ∀ᵐ Q ∂(ν : Measure (CompactArray CompactJointOverlap)), 0≤(Q 0 1).1.val)
--       (g : Jet3) (η : ProbabilityMeasure (FreshPartitionRange g.f))
--       (hm : ∀ r, (∫ x, x.val^r ∂(η : Measure (FreshPartitionRange g.f)))=
--         ∫ Q, freshReplicaArrayKernel (expBCF 1 g.f) r Q ∂(ν : Measure _))
--       (P : Measure BrownianPath) [IsProbabilityMeasure P] (hB : IsBrownianReal brownianEval P) :
--       (∫ x, Real.log x.val ∂(η : Measure (FreshPartitionRange g.f)))=
--         controlValue P g.f (quantileTrial (boundedQuantile ((compactPositivePairLaw ν).map Prod.fst)))
--   ```
--
--   **Definitions.** The statement is written with `OAI.SphericalPerceptronFreeEnergy.CompactArray`, `OAI.SphericalPerceptronFreeEnergy.CompactBlock`, `OAI.SphericalPerceptronFreeEnergy.CompactJointOverlap`, `OAI.SphericalPerceptronFreeEnergy.CompactOverlap`, `OAI.SphericalPerceptronFreeEnergy.CompactSpinGeometry`, `OAI.SphericalPerceptronFreeEnergy.FreshPartitionRange`, `OAI.SphericalPerceptronFreeEnergy.Jet3`, `OAI.SphericalPerceptronFreeEnergy.boundedQuantile`, `OAI.SphericalPerceptronFreeEnergy.compactGGDefect`, `OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw`, `OAI.SphericalPerceptronFreeEnergy.expBCF` and `OAI.SphericalPerceptronFreeEnergy.freshReplicaArrayKernel` (definitions bundle `OAIQ61Pf000` of this split); `OAI.SphericalPerceptronFreeEnergy.quantileTrial` (definitions bundle `OAIQ61Pf002` of this split); `OAI.SphericalPerceptronFreeEnergy.BrownianPath`, `OAI.SphericalPerceptronFreeEnergy.Time`, `OAI.SphericalPerceptronFreeEnergy.brownianEval`, `OAI.SphericalPerceptronFreeEnergy.controlValue` and `OAI.SphericalPerceptronFreeEnergy.instMeasurableSpaceBrownianPath` (the published bundle `Def_PerceptronFreeEnergy`).
--
--   **Used by.** The proof of `OAI.SphericalPerceptronFreeEnergy.main` of this split imports it.
-- source:
--   OpenAI, Spherical perceptron free energy (OpenAI result family 222), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 222; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/PerceptronFreeEnergy.lean; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/Perceptron/Control/FreshControl.lean (declaration OAI.SphericalPerceptronFreeEnergy.compactGG_freshLog_control)

import Mathlib
import Definitions.Def_PerceptronFreeEnergy
import Definitions.Def_OAIQ61Pf002

section

attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.markedTimePair_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

theorem compactGG_freshLog_control (ν : ProbabilityMeasure (CompactArray CompactJointOverlap))
    (hGG : ∀ (r : ℕ) (i : Fin r) (G : CompactBlock CompactJointOverlap r →ᵇ ℝ)
      (a : CompactJointOverlap →ᵇ ℝ), compactGGDefect ν r i G a=0)
    (hgeo : ∀ᵐ Q ∂(ν : Measure (CompactArray CompactJointOverlap)), CompactSpinGeometry Q)
    (hn : ∀ᵐ Q ∂(ν : Measure (CompactArray CompactJointOverlap)), 0≤(Q 0 1).1.val)
    (g : Jet3) (η : ProbabilityMeasure (FreshPartitionRange g.f))
    (hm : ∀ r, (∫ x, x.val^r ∂(η : Measure (FreshPartitionRange g.f)))=
      ∫ Q, freshReplicaArrayKernel (expBCF 1 g.f) r Q ∂(ν : Measure _))
    (P : Measure BrownianPath) [IsProbabilityMeasure P] (hB : IsBrownianReal brownianEval P) :
    (∫ x, Real.log x.val ∂(η : Measure (FreshPartitionRange g.f)))=
      controlValue P g.f (quantileTrial (boundedQuantile ((compactPositivePairLaw ν).map Prod.fst))) := by
  sorry

end SphericalPerceptronFreeEnergy
end

end OAI
end
