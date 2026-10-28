-- Prove2me | Theorems.Thm_OAI_SphericalPerceptronFreeEnergy_bulk_marked_self_consistency
-- name    : OAI.SphericalPerceptronFreeEnergy.bulk_marked_self_consistency
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T22:04:46.661662+00:00
-- url     : https://prove2.me/theorems/12c0f276-c83b-46a3-8848-3580f32ccf2f
-- title:
--   OAI.SphericalPerceptronFreeEnergy.bulk_marked_self_consistency: intermediate lemma from OpenAI, Spherical perceptron free energy (OpenAI result family 222)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SphericalPerceptronFreeEnergy.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Spherical perceptron free energy (OpenAI result family 222)*, OpenAI Math Release, September 24, 2026, result family 222, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SphericalPerceptronFreeEnergy.bulk_marked_self_consistency` of [lean/OAI/Probability/Perceptron/Cavity/BulkMarkedSelfConsistency.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/Perceptron/Cavity/BulkMarkedSelfConsistency.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SphericalPerceptronFreeEnergy`, with `open MeasureTheory ProbabilityTheory Filter Set`, `open scoped Topology BoundedContinuousFunction ContDiff`):
--
--   ```lean
--   theorem bulk_marked_self_consistency (M : ℕ→ℕ) (g : Jet3) (v : ℕ→ℕ→ℝ)
--       (hv : ∀ n p,1≤v n p) {C : ℝ} (hC : 0≤C) (hvC : ∀ n p,|v n (p+1)|≤C)
--       (hdO : ∀ p,Tendsto (fun n=>bulkDeviationAt n (M n) g.f p (v n)) atTop (𝓝 0))
--       (hdF : ∀ p,Tendsto (fun n=>bulkDeviationAt n (M n+2) g.f p (v n)) atTop (𝓝 0))
--       (s : ℕ→ℕ) (hs : StrictMono s) (α : ℝ) (hα : 0≤α)
--       (hd : Tendsto (fun n=>((M (s n)+2:ℕ):ℝ)/(s n+1:ℕ)) atTop (𝓝 α))
--       (ν : ProbabilityMeasure (CompactArray CompactOverlap))
--       (ho : Tendsto (fun n=>bulkGibbsArrayLaw (s n) (M (s n)) g.f (v (s n))) atTop (𝓝 ν))
--       (K : ℝ) (hK0 : 0≤K) (hK : ∀ n,((M (s n)+2:ℕ):ℝ)/(s n+1:ℕ)*‖g.d1‖^2≤K)
--       (μ : ProbabilityMeasure (CompactArray (BulkPairRange K)))
--       (hf : Tendsto (fun n=>bulkMarkedArrayLaw (s n) (M (s n)+2) g (v (s n)) K (hK n)) atTop (𝓝 μ)) :
--       ∃ a : ℝ→ℝ,Monotone a ∧ (∀ r,0≤a r ∧ a r≤α*‖g.d1‖^2) ∧
--         (∀ᵐ Q ∂(μ : Measure (CompactArray (BulkPairRange K))),∀ i j,i≠j→(Q i j).2.val=a (Q i j).1.val) ∧
--         (∀ᵐ x : Time ∂((markedTimeLaw K μ : Measure (CompactArray Time)).map (fun Q=>Q 0 1)),
--           a x=∫ y in 0..(x:ℝ),(realTail ((markedTimeLaw K μ : Measure (CompactArray Time)).map (fun Q=>Q 0 1)) y)⁻¹^2) ∧
--         ∀ᵐ x : Time ∂((markedTimeLaw K μ : Measure (CompactArray Time)).map (fun Q=>Q 0 1)),
--           (x:ℝ)≤(α*‖g.d1‖^2)/(1+α*‖g.d1‖^2)
--   ```
--
--   **Definitions.** The statement is written with `OAI.SphericalPerceptronFreeEnergy.BulkPairRange`, `OAI.SphericalPerceptronFreeEnergy.CompactArray`, `OAI.SphericalPerceptronFreeEnergy.CompactOverlap`, `OAI.SphericalPerceptronFreeEnergy.Jet3`, `OAI.SphericalPerceptronFreeEnergy.bulkDeviationAt`, `OAI.SphericalPerceptronFreeEnergy.bulkGibbsArrayLaw`, `OAI.SphericalPerceptronFreeEnergy.bulkMarkedArrayLaw`, `OAI.SphericalPerceptronFreeEnergy.markedTimeLaw` and `OAI.SphericalPerceptronFreeEnergy.realTail` (definitions bundle `OAIQ61Pf000` of this split); `OAI.SphericalPerceptronFreeEnergy.Time` (the published bundle `Def_PerceptronFreeEnergy`).
--
--   **Used by.** The proof of `OAI.SphericalPerceptronFreeEnergy.bulk_cavity_data` of this split imports it.
-- source:
--   OpenAI, Spherical perceptron free energy (OpenAI result family 222), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 222; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/PerceptronFreeEnergy.lean; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/Perceptron/Cavity/BulkMarkedSelfConsistency.lean (declaration OAI.SphericalPerceptronFreeEnergy.bulk_marked_self_consistency)

import Mathlib
import Definitions.Def_PerceptronFreeEnergy
import Definitions.Def_OAIQ61Pf000

section

attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.markedTimePair_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BoundedContinuousFunction ContDiff
namespace SphericalPerceptronFreeEnergy

theorem bulk_marked_self_consistency (M : ℕ→ℕ) (g : Jet3) (v : ℕ→ℕ→ℝ)
    (hv : ∀ n p,1≤v n p) {C : ℝ} (hC : 0≤C) (hvC : ∀ n p,|v n (p+1)|≤C)
    (hdO : ∀ p,Tendsto (fun n=>bulkDeviationAt n (M n) g.f p (v n)) atTop (𝓝 0))
    (hdF : ∀ p,Tendsto (fun n=>bulkDeviationAt n (M n+2) g.f p (v n)) atTop (𝓝 0))
    (s : ℕ→ℕ) (hs : StrictMono s) (α : ℝ) (hα : 0≤α)
    (hd : Tendsto (fun n=>((M (s n)+2:ℕ):ℝ)/(s n+1:ℕ)) atTop (𝓝 α))
    (ν : ProbabilityMeasure (CompactArray CompactOverlap))
    (ho : Tendsto (fun n=>bulkGibbsArrayLaw (s n) (M (s n)) g.f (v (s n))) atTop (𝓝 ν))
    (K : ℝ) (hK0 : 0≤K) (hK : ∀ n,((M (s n)+2:ℕ):ℝ)/(s n+1:ℕ)*‖g.d1‖^2≤K)
    (μ : ProbabilityMeasure (CompactArray (BulkPairRange K)))
    (hf : Tendsto (fun n=>bulkMarkedArrayLaw (s n) (M (s n)+2) g (v (s n)) K (hK n)) atTop (𝓝 μ)) :
    ∃ a : ℝ→ℝ,Monotone a ∧ (∀ r,0≤a r ∧ a r≤α*‖g.d1‖^2) ∧
      (∀ᵐ Q ∂(μ : Measure (CompactArray (BulkPairRange K))),∀ i j,i≠j→(Q i j).2.val=a (Q i j).1.val) ∧
      (∀ᵐ x : Time ∂((markedTimeLaw K μ : Measure (CompactArray Time)).map (fun Q=>Q 0 1)),
        a x=∫ y in 0..(x:ℝ),(realTail ((markedTimeLaw K μ : Measure (CompactArray Time)).map (fun Q=>Q 0 1)) y)⁻¹^2) ∧
      ∀ᵐ x : Time ∂((markedTimeLaw K μ : Measure (CompactArray Time)).map (fun Q=>Q 0 1)),
        (x:ℝ)≤(α*‖g.d1‖^2)/(1+α*‖g.d1‖^2) := by
  sorry

end SphericalPerceptronFreeEnergy
end

end OAI
end
