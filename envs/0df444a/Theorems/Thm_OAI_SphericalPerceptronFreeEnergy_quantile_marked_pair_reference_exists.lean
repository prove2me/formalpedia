-- Prove2me | Theorems.Thm_OAI_SphericalPerceptronFreeEnergy_quantile_marked_pair_reference_exists
-- name    : OAI.SphericalPerceptronFreeEnergy.quantile_marked_pair_reference_exists
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T22:09:36.538121+00:00
-- url     : https://prove2.me/theorems/356363dc-96b9-4ae4-ba73-3663a25f11d3
-- title:
--   OAI.SphericalPerceptronFreeEnergy.quantile_marked_pair_reference_exists: intermediate lemma from OpenAI, Spherical perceptron free energy (OpenAI result family 222)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SphericalPerceptronFreeEnergy.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Spherical perceptron free energy (OpenAI result family 222)*, OpenAI Math Release, September 24, 2026, result family 222, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SphericalPerceptronFreeEnergy.quantile_marked_pair_reference_exists` of [lean/OAI/Probability/Perceptron/Variational/RoundedMarkedReference.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/Perceptron/Variational/RoundedMarkedReference.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SphericalPerceptronFreeEnergy`, with `open MeasureTheory ProbabilityTheory Set Filter`, `open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction`):
--
--   ```lean
--   theorem quantile_marked_pair_reference_exists (q : Time→Time) (hq : Monotone q)
--       (g : Jet3) (v : ℝ→ᵇℝ) : ∃ a : ℝ→ℝ, Monotone a ∧ (∀ r,0≤a r ∧ a r≤‖v‖^2) ∧
--         ∀ (F : CompactOverlap→ᵇℝ) (b : Bool),
--       ∃ (ν : ProbabilityMeasure (CompactArray CompactJointOverlap))
--         (η : ProbabilityMeasure (WeightedRestorationRange g.f (pairRestorationBound g.f v (secondPairMark v b) F))),
--         (∀ (r : ℕ) (i : Fin r) (G : CompactBlock CompactJointOverlap r →ᵇ ℝ)
--           (a : CompactJointOverlap →ᵇ ℝ), compactGGDefect ν r i G a=0) ∧
--         (∀ᵐ Q ∂(ν : Measure (CompactArray CompactJointOverlap)), CompactSpinGeometry Q) ∧
--         (ν : Measure (CompactArray CompactJointOverlap)).map (fun Q => (Q 0 1).1)=
--           (quantileSpinLaw q hq.measurable : Measure CompactOverlap) ∧
--         (∀ j,(∫ x,x.1.val*x.2.val^j
--           ∂(η : Measure (WeightedRestorationRange g.f (pairRestorationBound g.f v (secondPairMark v b) F))))=
--           ∫ Q : CompactArray CompactJointOverlap,scalarRestorationPairMoment g.f v (secondPairMark v b) F j
--             (fun i l => (Q i l).1.val) ∂(ν : Measure _)) ∧
--         (∫ x,x.1.val*restorationReciprocal g.f 2 x.2
--           ∂(η : Measure (WeightedRestorationRange g.f (pairRestorationBound g.f v (secondPairMark v b) F))))=
--             ∫ u,F (timeSpin (q u))*(a (q u))^(pairMarkPower b) ∂timeLaw
--   ```
--
--   **Definitions.** The statement is written with `OAI.SphericalPerceptronFreeEnergy.CompactArray`, `OAI.SphericalPerceptronFreeEnergy.CompactBlock`, `OAI.SphericalPerceptronFreeEnergy.CompactJointOverlap`, `OAI.SphericalPerceptronFreeEnergy.CompactOverlap`, `OAI.SphericalPerceptronFreeEnergy.CompactSpinGeometry`, `OAI.SphericalPerceptronFreeEnergy.Jet3`, `OAI.SphericalPerceptronFreeEnergy.RestorationRange`, `OAI.SphericalPerceptronFreeEnergy.WeightedRestorationRange` and `OAI.SphericalPerceptronFreeEnergy.compactGGDefect` (definitions bundle `OAIQ61Pf000` of this split); `OAI.SphericalPerceptronFreeEnergy.pairMarkPower` and `OAI.SphericalPerceptronFreeEnergy.secondPairMark` (definitions bundle `OAIQ61Pf001` of this split); `OAI.SphericalPerceptronFreeEnergy.pairRestorationBound`, `OAI.SphericalPerceptronFreeEnergy.quantileSpinLaw`, `OAI.SphericalPerceptronFreeEnergy.restorationReciprocal`, `OAI.SphericalPerceptronFreeEnergy.scalarRestorationPairMoment` and `OAI.SphericalPerceptronFreeEnergy.timeSpin` (definitions bundle `OAIQ61Pf002` of this split); `OAI.SphericalPerceptronFreeEnergy.Time` and `OAI.SphericalPerceptronFreeEnergy.timeLaw` (the published bundle `Def_PerceptronFreeEnergy`).
--
--   **Used by.** The proof of `OAI.SphericalPerceptronFreeEnergy.bulk_marked_self_consistency` of this split imports it.
-- source:
--   OpenAI, Spherical perceptron free energy (OpenAI result family 222), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 222; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/PerceptronFreeEnergy.lean; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/Perceptron/Variational/RoundedMarkedReference.lean (declaration OAI.SphericalPerceptronFreeEnergy.quantile_marked_pair_reference_exists)

import Mathlib
import Definitions.Def_PerceptronFreeEnergy
import Definitions.Def_OAIQ61Pf002

section

attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_fst_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.markedTimePair_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction

theorem quantile_marked_pair_reference_exists (q : Time→Time) (hq : Monotone q)
    (g : Jet3) (v : ℝ→ᵇℝ) : ∃ a : ℝ→ℝ, Monotone a ∧ (∀ r,0≤a r ∧ a r≤‖v‖^2) ∧
      ∀ (F : CompactOverlap→ᵇℝ) (b : Bool),
    ∃ (ν : ProbabilityMeasure (CompactArray CompactJointOverlap))
      (η : ProbabilityMeasure (WeightedRestorationRange g.f (pairRestorationBound g.f v (secondPairMark v b) F))),
      (∀ (r : ℕ) (i : Fin r) (G : CompactBlock CompactJointOverlap r →ᵇ ℝ)
        (a : CompactJointOverlap →ᵇ ℝ), compactGGDefect ν r i G a=0) ∧
      (∀ᵐ Q ∂(ν : Measure (CompactArray CompactJointOverlap)), CompactSpinGeometry Q) ∧
      (ν : Measure (CompactArray CompactJointOverlap)).map (fun Q => (Q 0 1).1)=
        (quantileSpinLaw q hq.measurable : Measure CompactOverlap) ∧
      (∀ j,(∫ x,x.1.val*x.2.val^j
        ∂(η : Measure (WeightedRestorationRange g.f (pairRestorationBound g.f v (secondPairMark v b) F))))=
        ∫ Q : CompactArray CompactJointOverlap,scalarRestorationPairMoment g.f v (secondPairMark v b) F j
          (fun i l => (Q i l).1.val) ∂(ν : Measure _)) ∧
      (∫ x,x.1.val*restorationReciprocal g.f 2 x.2
        ∂(η : Measure (WeightedRestorationRange g.f (pairRestorationBound g.f v (secondPairMark v b) F))))=
          ∫ u,F (timeSpin (q u))*(a (q u))^(pairMarkPower b) ∂timeLaw := by
  sorry

end SphericalPerceptronFreeEnergy
end

end OAI
end
