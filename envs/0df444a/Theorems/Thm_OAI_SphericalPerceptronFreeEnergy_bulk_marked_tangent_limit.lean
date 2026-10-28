-- Prove2me | Theorems.Thm_OAI_SphericalPerceptronFreeEnergy_bulk_marked_tangent_limit
-- name    : OAI.SphericalPerceptronFreeEnergy.bulk_marked_tangent_limit
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T22:08:53.522637+00:00
-- url     : https://prove2.me/theorems/12588a14-0e60-4a2a-9077-47f1c1b487fa
-- title:
--   OAI.SphericalPerceptronFreeEnergy.bulk_marked_tangent_limit: intermediate lemma from OpenAI, Spherical perceptron free energy (OpenAI result family 222)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SphericalPerceptronFreeEnergy.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Spherical perceptron free energy (OpenAI result family 222)*, OpenAI Math Release, September 24, 2026, result family 222, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SphericalPerceptronFreeEnergy.bulk_marked_tangent_limit` of [lean/OAI/Probability/Perceptron/Cavity/BulkMarkedTangentLimit.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/Perceptron/Cavity/BulkMarkedTangentLimit.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SphericalPerceptronFreeEnergy`, with `open MeasureTheory ProbabilityTheory Set Filter`, `open scoped BigOperators Topology BoundedContinuousFunction ContDiff`):
--
--   ```lean
--   lemma bulk_marked_tangent_limit (M : ℕ→ℕ) (f : Jet3) (v : ℕ→ℕ→ℝ)
--       {C : ℝ} (hC : 0≤C) (hv : ∀ n j,|v n (j+1)|≤C)
--       (K : ℝ) {s : ℕ→ℕ} (hs : StrictMono s)
--       (hK : ∀ n,M (s n)/(s n+1:ℕ)*‖f.d1‖^2≤K)
--       (μ : ProbabilityMeasure (CompactArray (BulkPairRange K)))
--       (hlim : Tendsto (fun n => bulkMarkedArrayLaw (s n) (M (s n)) f (v (s n)) K (hK n)) atTop (𝓝 μ))
--       (G : ℝ→ᵇℝ) (hG : ContDiff ℝ 1 (G : ℝ→ℝ)) :
--       (∫ Q,markedTangentR K G (compactBlock 2 Q) ∂(μ : Measure _))-
--         (∫ Q,markedTangentPair K G (compactBlock 2 Q) ∂(μ : Measure _))+
--         2*(∫ Q,markedTangentTriple K G (compactBlock 3 Q) ∂(μ : Measure _))=0
--   ```
--
--   **Definitions.** The statement is written with `OAI.SphericalPerceptronFreeEnergy.BulkPairRange`, `OAI.SphericalPerceptronFreeEnergy.CompactArray`, `OAI.SphericalPerceptronFreeEnergy.CompactBlock`, `OAI.SphericalPerceptronFreeEnergy.CompactOverlap`, `OAI.SphericalPerceptronFreeEnergy.Jet3`, `OAI.SphericalPerceptronFreeEnergy.bulkMarkedArrayLaw`, `OAI.SphericalPerceptronFreeEnergy.compactBlock`, `OAI.SphericalPerceptronFreeEnergy.markedTangentPair` and `OAI.SphericalPerceptronFreeEnergy.markedTangentR` (definitions bundle `OAIQ61Pf000` of this split); `OAI.SphericalPerceptronFreeEnergy.markedTangentTriple` (definitions bundle `OAIQ61Pf002` of this split).
--
--   **Used by.** The proof of `OAI.SphericalPerceptronFreeEnergy.bulk_marked_self_consistency` of this split imports it.
-- source:
--   OpenAI, Spherical perceptron free energy (OpenAI result family 222), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 222; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/PerceptronFreeEnergy.lean; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/Perceptron/Cavity/BulkMarkedTangentLimit.lean (declaration OAI.SphericalPerceptronFreeEnergy.bulk_marked_tangent_limit)

import Mathlib
import Definitions.Def_OAIQ61Pf002

section

attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.markedTimePair_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators Topology BoundedContinuousFunction ContDiff

lemma bulk_marked_tangent_limit (M : ℕ→ℕ) (f : Jet3) (v : ℕ→ℕ→ℝ)
    {C : ℝ} (hC : 0≤C) (hv : ∀ n j,|v n (j+1)|≤C)
    (K : ℝ) {s : ℕ→ℕ} (hs : StrictMono s)
    (hK : ∀ n,M (s n)/(s n+1:ℕ)*‖f.d1‖^2≤K)
    (μ : ProbabilityMeasure (CompactArray (BulkPairRange K)))
    (hlim : Tendsto (fun n => bulkMarkedArrayLaw (s n) (M (s n)) f (v (s n)) K (hK n)) atTop (𝓝 μ))
    (G : ℝ→ᵇℝ) (hG : ContDiff ℝ 1 (G : ℝ→ℝ)) :
    (∫ Q,markedTangentR K G (compactBlock 2 Q) ∂(μ : Measure _))-
      (∫ Q,markedTangentPair K G (compactBlock 2 Q) ∂(μ : Measure _))+
      2*(∫ Q,markedTangentTriple K G (compactBlock 3 Q) ∂(μ : Measure _))=0 := by
  sorry

end SphericalPerceptronFreeEnergy
end

end OAI
end
