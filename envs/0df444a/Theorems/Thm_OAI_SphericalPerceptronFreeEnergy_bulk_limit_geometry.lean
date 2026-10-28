-- Prove2me | Theorems.Thm_OAI_SphericalPerceptronFreeEnergy_bulk_limit_geometry
-- name    : OAI.SphericalPerceptronFreeEnergy.bulk_limit_geometry
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T22:02:39.061986+00:00
-- url     : https://prove2.me/theorems/18581105-0778-4fe5-b9db-c1b14e62428c
-- title:
--   OAI.SphericalPerceptronFreeEnergy.bulk_limit_geometry: intermediate lemma from OpenAI, Spherical perceptron free energy (OpenAI result family 222)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SphericalPerceptronFreeEnergy.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Spherical perceptron free energy (OpenAI result family 222)*, OpenAI Math Release, September 24, 2026, result family 222, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SphericalPerceptronFreeEnergy.bulk_limit_geometry` of [lean/OAI/Probability/Perceptron/Cavity/BulkEmpiricalLimit.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/Perceptron/Cavity/BulkEmpiricalLimit.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SphericalPerceptronFreeEnergy`, with `open MeasureTheory ProbabilityTheory Filter Set`, `open scoped Topology BoundedContinuousFunction NNReal ENNReal BigOperators`):
--
--   ```lean
--   lemma bulk_limit_geometry (M : ℕ→ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℕ→ℝ)
--       (hv : ∀ᶠ n in atTop, ∀ p, 1≤v n p)
--       (hd : ∀ p, Tendsto (fun n => bulkDeviationAt n (M n) f p (v n)) atTop (𝓝 0))
--       {ν : ProbabilityMeasure (CompactArray CompactOverlap)} {s : ℕ→ℕ} (hs : StrictMono s)
--       (hlim : Tendsto (fun n => bulkGibbsArrayLaw (s n) (M (s n)) f (v (s n))) atTop (𝓝 ν)) :
--       (∀ᵐ Q ∂(bulkJointLaw ν : Measure (CompactArray CompactJointOverlap)), CompactSpinGeometry Q) ∧
--       (∀ᵐ Q : CompactArray CompactJointOverlap ∂(bulkJointLaw ν : Measure _), 0≤(Q 0 1).1.val) ∧
--       (∀ r (i : Fin r) (F : CompactBlock CompactJointOverlap r→ᵇℝ) (g : CompactJointOverlap→ᵇℝ),
--         compactGGDefect (bulkJointLaw ν) r i F g=0)
--   ```
--
--   **Definitions.** The statement is written with `OAI.SphericalPerceptronFreeEnergy.CompactArray`, `OAI.SphericalPerceptronFreeEnergy.CompactBlock`, `OAI.SphericalPerceptronFreeEnergy.CompactJointOverlap`, `OAI.SphericalPerceptronFreeEnergy.CompactOverlap`, `OAI.SphericalPerceptronFreeEnergy.CompactSpinGeometry`, `OAI.SphericalPerceptronFreeEnergy.bulkDeviationAt`, `OAI.SphericalPerceptronFreeEnergy.bulkGibbsArrayLaw`, `OAI.SphericalPerceptronFreeEnergy.bulkJointLaw` and `OAI.SphericalPerceptronFreeEnergy.compactGGDefect` (definitions bundle `OAIQ61Pf000` of this split).
--
--   **Used by.** The proofs of `OAI.SphericalPerceptronFreeEnergy.bulk_cavity_data` and `OAI.SphericalPerceptronFreeEnergy.bulk_marked_self_consistency` of this split import it.
-- source:
--   OpenAI, Spherical perceptron free energy (OpenAI result family 222), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 222; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/PerceptronFreeEnergy.lean; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/Perceptron/Cavity/BulkEmpiricalLimit.lean (declaration OAI.SphericalPerceptronFreeEnergy.bulk_limit_geometry)

import Mathlib
import Definitions.Def_OAIQ61Pf000

section

attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.markedTimePair_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BoundedContinuousFunction NNReal ENNReal BigOperators

lemma bulk_limit_geometry (M : ℕ→ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℕ→ℝ)
    (hv : ∀ᶠ n in atTop, ∀ p, 1≤v n p)
    (hd : ∀ p, Tendsto (fun n => bulkDeviationAt n (M n) f p (v n)) atTop (𝓝 0))
    {ν : ProbabilityMeasure (CompactArray CompactOverlap)} {s : ℕ→ℕ} (hs : StrictMono s)
    (hlim : Tendsto (fun n => bulkGibbsArrayLaw (s n) (M (s n)) f (v (s n))) atTop (𝓝 ν)) :
    (∀ᵐ Q ∂(bulkJointLaw ν : Measure (CompactArray CompactJointOverlap)), CompactSpinGeometry Q) ∧
    (∀ᵐ Q : CompactArray CompactJointOverlap ∂(bulkJointLaw ν : Measure _), 0≤(Q 0 1).1.val) ∧
    (∀ r (i : Fin r) (F : CompactBlock CompactJointOverlap r→ᵇℝ) (g : CompactJointOverlap→ᵇℝ),
      compactGGDefect (bulkJointLaw ν) r i F g=0) := by
  sorry

end SphericalPerceptronFreeEnergy
end

end OAI
end
