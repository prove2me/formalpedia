-- Prove2me | Theorems.Thm_OAI_SphericalPerceptronFreeEnergy_labelProfile_reference_full_exists
-- name    : OAI.SphericalPerceptronFreeEnergy.labelProfile_reference_full_exists
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T22:11:02.27445+00:00
-- url     : https://prove2.me/theorems/e3550460-4c78-4488-9ce2-2689de7cbe98
-- title:
--   OAI.SphericalPerceptronFreeEnergy.labelProfile_reference_full_exists: intermediate lemma from OpenAI, Spherical perceptron free energy (OpenAI result family 222)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SphericalPerceptronFreeEnergy.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Spherical perceptron free energy (OpenAI result family 222)*, OpenAI Math Release, September 24, 2026, result family 222, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SphericalPerceptronFreeEnergy.labelProfile_reference_full_exists` of [lean/OAI/Probability/Perceptron/Variational/LabelProfileReferenceFull.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/Perceptron/Variational/LabelProfileReferenceFull.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SphericalPerceptronFreeEnergy`, with `open MeasureTheory ProbabilityTheory Set Filter`, `open scoped Topology ENNReal NNReal BigOperators BoundedContinuousFunction`):
--
--   ```lean
--   theorem labelProfile_reference_full_exists (k : ℕ) (w : Fin (k+1)→ℝ)
--       (hw : ∀ l, 0<w l) (hw1 : ∑ l,w l=1)
--       (q : Fin (k+1)→Time) (hq : Monotone q) (g : Jet3) :
--       ∃ (ν : ProbabilityMeasure (CompactArray CompactJointOverlap))
--         (η : ProbabilityMeasure (FreshPartitionRange g.f)),
--         (∀ (r : ℕ) (i : Fin r) (G : CompactBlock CompactJointOverlap r →ᵇ ℝ)
--           (a : CompactJointOverlap →ᵇ ℝ), compactGGDefect ν r i G a=0) ∧
--         (∀ᵐ Q ∂(ν : Measure (CompactArray CompactJointOverlap)), CompactSpinGeometry Q) ∧
--         (∀ F : CompactOverlap →ᵇ ℝ,
--           (∫ Q : CompactArray CompactJointOverlap, F (Q 0 1).1 ∂(ν : Measure _))=∑ l,w l*F (timeSpin (q l))) ∧
--         (∀ r, (∫ x, x.val^r ∂(η : Measure (FreshPartitionRange g.f)))=
--           ∫ Q, freshReplicaArrayKernel (expBCF 1 g.f) r Q ∂(ν : Measure _)) ∧
--         (∫ x, Real.log x.val ∂(η : Measure (FreshPartitionRange g.f)))=
--           labelProfileValue k (stepCumulative w) (fun i => (q i:ℝ)) (q (Fin.last k)).prop.2 g
--   ```
--
--   **Definitions.** The statement is written with `OAI.SphericalPerceptronFreeEnergy.CompactArray`, `OAI.SphericalPerceptronFreeEnergy.CompactBlock`, `OAI.SphericalPerceptronFreeEnergy.CompactJointOverlap`, `OAI.SphericalPerceptronFreeEnergy.CompactOverlap`, `OAI.SphericalPerceptronFreeEnergy.CompactSpinGeometry`, `OAI.SphericalPerceptronFreeEnergy.FreshPartitionRange`, `OAI.SphericalPerceptronFreeEnergy.Jet3`, `OAI.SphericalPerceptronFreeEnergy.compactGGDefect`, `OAI.SphericalPerceptronFreeEnergy.expBCF`, `OAI.SphericalPerceptronFreeEnergy.freshReplicaArrayKernel`, `OAI.SphericalPerceptronFreeEnergy.labelProfileValue` and `OAI.SphericalPerceptronFreeEnergy.stepCumulative` (definitions bundle `OAIQ61Pf000` of this split); `OAI.SphericalPerceptronFreeEnergy.timeSpin` (definitions bundle `OAIQ61Pf002` of this split); `OAI.SphericalPerceptronFreeEnergy.Time` (the published bundle `Def_PerceptronFreeEnergy`).
--
--   **Used by.** The proof of `OAI.SphericalPerceptronFreeEnergy.compactGG_freshLog_control` of this split imports it.
-- source:
--   OpenAI, Spherical perceptron free energy (OpenAI result family 222), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 222; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/PerceptronFreeEnergy.lean; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/Perceptron/Variational/LabelProfileReferenceFull.lean (declaration OAI.SphericalPerceptronFreeEnergy.labelProfile_reference_full_exists)

import Mathlib
import Definitions.Def_PerceptronFreeEnergy
import Definitions.Def_OAIQ61Pf002

section

attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_fst_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instCoeFunBoundedFieldForallElemRealTime _root_.OAI.SphericalPerceptronFreeEnergy.markedTimePair_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

theorem labelProfile_reference_full_exists (k : ℕ) (w : Fin (k+1)→ℝ)
    (hw : ∀ l, 0<w l) (hw1 : ∑ l,w l=1)
    (q : Fin (k+1)→Time) (hq : Monotone q) (g : Jet3) :
    ∃ (ν : ProbabilityMeasure (CompactArray CompactJointOverlap))
      (η : ProbabilityMeasure (FreshPartitionRange g.f)),
      (∀ (r : ℕ) (i : Fin r) (G : CompactBlock CompactJointOverlap r →ᵇ ℝ)
        (a : CompactJointOverlap →ᵇ ℝ), compactGGDefect ν r i G a=0) ∧
      (∀ᵐ Q ∂(ν : Measure (CompactArray CompactJointOverlap)), CompactSpinGeometry Q) ∧
      (∀ F : CompactOverlap →ᵇ ℝ,
        (∫ Q : CompactArray CompactJointOverlap, F (Q 0 1).1 ∂(ν : Measure _))=∑ l,w l*F (timeSpin (q l))) ∧
      (∀ r, (∫ x, x.val^r ∂(η : Measure (FreshPartitionRange g.f)))=
        ∫ Q, freshReplicaArrayKernel (expBCF 1 g.f) r Q ∂(ν : Measure _)) ∧
      (∫ x, Real.log x.val ∂(η : Measure (FreshPartitionRange g.f)))=
        labelProfileValue k (stepCumulative w) (fun i => (q i:ℝ)) (q (Fin.last k)).prop.2 g := by
  sorry

end SphericalPerceptronFreeEnergy
end

end OAI
end
