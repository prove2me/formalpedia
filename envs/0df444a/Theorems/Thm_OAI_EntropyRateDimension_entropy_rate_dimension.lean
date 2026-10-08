-- Prove2me | Theorems.Thm_OAI_EntropyRateDimension_entropy_rate_dimension
-- name    : OAI.EntropyRateDimension.entropy_rate_dimension
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:32:37.383722+00:00
-- url     : https://prove2.me/theorems/2c8a3fbc-f038-40c8-8db5-58f16380edc9
-- statement:
--   The theorem states that, for a finite nonempty index type ι, a system S of affine contractions of the real line, and a Borel probability measure μ on ℝ that is self-similar for S, the lower Hausdorff dimension of μ equals ofReal(min(1, h/λ)), where h is the entropy rate and λ the Lyapunov exponent of S. The system S consists of ratios rᵢ and offsets bᵢ with 0<|rᵢ|<1, together with positive weights wᵢ summing to 1, and acts by fᵢ(x)=rᵢx+bᵢ. Self-similarity of μ means μ=∑ᵢ wᵢ·(fᵢ)_*μ, the weighted sum of the pushforwards of μ under the maps. For a word of length n, the composed map is the corresponding composition of the fᵢ, represented by its pair (product of ratios, resulting offset), and the word weight is the product of the weights of its letters. The mass of a composed map g is the total weight of all length-n words giving g, and the walk entropy H_n is the Shannon entropy in bits of this distribution over distinct composed maps, namely ∑ −m log m divided by log 2. The entropy rate is the infimum over n≥1 of H_n/n, and the Lyapunov exponent is −∑ᵢ wᵢ log₂|rᵢ|. The lower Hausdorff dimension of μ is the infimum of dim_H(E) over measurable sets E with μ(E)>0, valued in [0,∞]. The conclusion identifies this with the extended-nonnegative-real number given by the real min(1, h/λ).
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/SelfSimilar.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/SelfSimilar.lean; bytes 1949..2217
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_SelfSimilar

namespace OAI

universe uι

open scoped BigOperators ENNReal

open MeasureTheory

namespace EntropyRateDimension

open MeasureTheory

theorem entropy_rate_dimension {ι : Type uι} [Fintype ι] [Nonempty ι]
    (S : System ι) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : S.SelfSimilar μ) :
    lowerHausdorffDimension μ = ENNReal.ofReal (min 1 (S.entropyRate / S.lyapunov)) := by
  sorry

end EntropyRateDimension
end OAI
