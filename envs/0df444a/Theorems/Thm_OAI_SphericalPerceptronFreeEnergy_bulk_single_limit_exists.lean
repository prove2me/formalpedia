-- Prove2me | Theorems.Thm_OAI_SphericalPerceptronFreeEnergy_bulk_single_limit_exists
-- name    : OAI.SphericalPerceptronFreeEnergy.bulk_single_limit_exists
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T22:04:33.517153+00:00
-- url     : https://prove2.me/theorems/a60508b8-71df-41a5-a1e3-05dc31cbe6d2
-- title:
--   OAI.SphericalPerceptronFreeEnergy.bulk_single_limit_exists: intermediate lemma from OpenAI, Spherical perceptron free energy (OpenAI result family 222)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SphericalPerceptronFreeEnergy.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Spherical perceptron free energy (OpenAI result family 222)*, OpenAI Math Release, September 24, 2026, result family 222, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SphericalPerceptronFreeEnergy.bulk_single_limit_exists` of [lean/OAI/Probability/Perceptron/Cavity/BulkSingleLimit.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/Perceptron/Cavity/BulkSingleLimit.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SphericalPerceptronFreeEnergy`, with `open MeasureTheory ProbabilityTheory Set Filter`, `open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction`):
--
--   ```lean
--   theorem bulk_single_limit_exists (M : ℕ→ℕ) (g : Jet3) (v : ℕ→ℕ→ℝ) (s : ℕ→ℕ)
--       {ν : ProbabilityMeasure (CompactArray CompactOverlap)}
--       (hlim : Tendsto (fun n => bulkGibbsArrayLaw (s n) (M (s n)) g.f (v (s n))) atTop (𝓝 ν))
--       (hGG : ∀ (r : ℕ) (i : Fin r) (G : CompactBlock CompactJointOverlap r →ᵇ ℝ)
--         (a : CompactJointOverlap →ᵇ ℝ), compactGGDefect (bulkJointLaw ν) r i G a=0)
--       (hgeo : ∀ᵐ Q ∂(bulkJointLaw ν : Measure (CompactArray CompactJointOverlap)), CompactSpinGeometry Q)
--       (hn : ∀ᵐ Q ∂(bulkJointLaw ν : Measure (CompactArray CompactJointOverlap)), 0≤(Q 0 1).1.val)
--       (w : ℝ→ᵇℝ) : ∃ c : ℝ, |c|≤‖w‖ ∧ ∀ b : Bool,
--       Tendsto (fun n => ∫ p,bulkFreshNumerator (s n) (M (s n)) 1 g.f (v (s n))
--         1 (gaussianMixedTest (fun _=>w)) (gaussianMixedTest (fun _=>secondPairMark w b)) p /
--         bulkFreshDenominator (s n) (M (s n)) g.f (v (s n)) p^1
--           ∂twoFreshDisorderLaw (s n+1) (M (s n))) atTop (𝓝 (c^(pairMarkPower b)))
--   ```
--
--   **Definitions.** The statement is written with `OAI.SphericalPerceptronFreeEnergy.BulkDisorder`, `OAI.SphericalPerceptronFreeEnergy.BulkMark`, `OAI.SphericalPerceptronFreeEnergy.CompactArray`, `OAI.SphericalPerceptronFreeEnergy.CompactBlock`, `OAI.SphericalPerceptronFreeEnergy.CompactJointOverlap`, `OAI.SphericalPerceptronFreeEnergy.CompactOverlap`, `OAI.SphericalPerceptronFreeEnergy.CompactSpinGeometry`, `OAI.SphericalPerceptronFreeEnergy.EnrichedIndex`, `OAI.SphericalPerceptronFreeEnergy.Jet3`, `OAI.SphericalPerceptronFreeEnergy.TwoFreshDisorder`, `OAI.SphericalPerceptronFreeEnergy.bulkDegree`, `OAI.SphericalPerceptronFreeEnergy.bulkFreshDenominator`, `OAI.SphericalPerceptronFreeEnergy.bulkFreshNumerator`, `OAI.SphericalPerceptronFreeEnergy.bulkGibbsArrayLaw`, `OAI.SphericalPerceptronFreeEnergy.bulkJointLaw`, `OAI.SphericalPerceptronFreeEnergy.compactGGDefect`, `OAI.SphericalPerceptronFreeEnergy.gaussianMixedTest` and `OAI.SphericalPerceptronFreeEnergy.twoFreshDisorderLaw` (definitions bundle `OAIQ61Pf000` of this split); `OAI.SphericalPerceptronFreeEnergy.pairMarkPower` and `OAI.SphericalPerceptronFreeEnergy.secondPairMark` (definitions bundle `OAIQ61Pf001` of this split).
--
--   **Used by.** The proof of `OAI.SphericalPerceptronFreeEnergy.bulk_cavity_data` of this split imports it.
-- source:
--   OpenAI, Spherical perceptron free energy (OpenAI result family 222), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 222; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/PerceptronFreeEnergy.lean; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/Perceptron/Cavity/BulkSingleLimit.lean (declaration OAI.SphericalPerceptronFreeEnergy.bulk_single_limit_exists)

import Mathlib
import Definitions.Def_OAIQ61Pf000
import Definitions.Def_OAIQ61Pf001

section

attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.bulkFiniteReplicaLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw _root_.OAI.SphericalPerceptronFreeEnergy.markedTimePair_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction

theorem bulk_single_limit_exists (M : ℕ→ℕ) (g : Jet3) (v : ℕ→ℕ→ℝ) (s : ℕ→ℕ)
    {ν : ProbabilityMeasure (CompactArray CompactOverlap)}
    (hlim : Tendsto (fun n => bulkGibbsArrayLaw (s n) (M (s n)) g.f (v (s n))) atTop (𝓝 ν))
    (hGG : ∀ (r : ℕ) (i : Fin r) (G : CompactBlock CompactJointOverlap r →ᵇ ℝ)
      (a : CompactJointOverlap →ᵇ ℝ), compactGGDefect (bulkJointLaw ν) r i G a=0)
    (hgeo : ∀ᵐ Q ∂(bulkJointLaw ν : Measure (CompactArray CompactJointOverlap)), CompactSpinGeometry Q)
    (hn : ∀ᵐ Q ∂(bulkJointLaw ν : Measure (CompactArray CompactJointOverlap)), 0≤(Q 0 1).1.val)
    (w : ℝ→ᵇℝ) : ∃ c : ℝ, |c|≤‖w‖ ∧ ∀ b : Bool,
    Tendsto (fun n => ∫ p,bulkFreshNumerator (s n) (M (s n)) 1 g.f (v (s n))
      1 (gaussianMixedTest (fun _=>w)) (gaussianMixedTest (fun _=>secondPairMark w b)) p /
      bulkFreshDenominator (s n) (M (s n)) g.f (v (s n)) p^1
        ∂twoFreshDisorderLaw (s n+1) (M (s n))) atTop (𝓝 (c^(pairMarkPower b))) := by
  sorry

end SphericalPerceptronFreeEnergy
end

end OAI
end
