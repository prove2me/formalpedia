-- Prove2me | Theorems.Thm_OAI_EntropyRateDimension_Extensions_homogeneous_dimension_direct
-- name    : OAI.EntropyRateDimension.Extensions.homogeneous_dimension_direct
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:32:37.194108+00:00
-- url     : https://prove2.me/theorems/31a2a83c-c6c5-4812-ac28-a8e0b6c21adc
-- statement:
--   The theorem states that, for a finite nonempty index set ι, a self-similar system S consists of real ratios r_i with 0<|r_i|<1, real offsets, and positive weights summing to 1, giving affine maps x ↦ r_i x + offset_i on the real line. Suppose all ratios equal the same number λ>0 (so λ<1 by the system's constraints), μ is a Borel probability measure on ℝ that is self-similar for S, meaning μ equals the sum over i of the weight w_i times the pushforward of μ under the i-th affine map, and S has no exact overlaps, meaning the map sending each finite word of indices to the composed affine map (its pair of overall ratio and offset) is injective. Then the lower Hausdorff dimension of μ, defined as the infimum of the Hausdorff dimensions of measurable sets of positive μ-measure, equals ENNReal.ofReal of min(1, H/log(1/λ)), where H = Σ_i −w_i log w_i is the symbol entropy of the weights.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/SelfSimilarCorollaries.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/SelfSimilarCorollaries.lean; bytes 1228..1603
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_SelfSimilarCorollaries

namespace OAI

universe uι

section

open scoped BigOperators ENNReal

open MeasureTheory

namespace EntropyRateDimension

namespace Extensions

variable {ι : Type uι} [Fintype ι]

theorem homogeneous_dimension_direct {ι : Type uι} [Fintype ι] [Nonempty ι] (S : System ι)
    {lam : ℝ} (hlam : 0 < lam) (hr : ∀ i, S.ratio i = lam)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : S.SelfSimilar μ)
    (h : NoExactOverlaps S) :
    lowerHausdorffDimension μ =
      ENNReal.ofReal (min 1 (symbolEntropy S / Real.log (1/lam))) := by
  sorry

end Extensions
end EntropyRateDimension
end
end OAI
