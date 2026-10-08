-- Prove2me | Theorems.Thm_OAI_CorSetReference_cor_set
-- name    : OAI.CorSetReference.cor_set
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:32:29.573058+00:00
-- url     : https://prove2.me/theorems/0ab4d6f5-4dcd-429b-9af2-7bb249097b67
-- statement:
--   The theorem states that, for a finite nonempty index type ι and real numbers rᵢ and tᵢ with 0<|rᵢ|<1 for every i, the following hold under a no-overlap hypothesis. The attractor is defined as the set of all coding points of infinite sequences ω:ℕ→ι, where the coding point of ω is the sum over n≥0 of (r_{ω0}·…·r_{ω(n−1)})·t_{ωn}. For a finite list u of indices, word(r,t,u) is the pair (a,b) obtained by folding from the right starting at (1,0), replacing the current pair (a,b) by (r_i·a, r_i·b+t_i) for each symbol i, so that it records the coefficients of the composed affine map. The hypothesis is that word(r,t,u)=word(r,t,v) implies u=v for all nonempty lists u and v. Under it, the attractor is compact and nonempty, there is a unique real s≥0 with ∑ᵢ|rᵢ|^s=1, and for every real s≥0 satisfying ∑ᵢ|rᵢ|^s=1, the Hausdorff dimension of the attractor equals ENNReal.ofReal(min(1,s)), that is, min(1,s) as an extended nonnegative real. The result is stated with its proof admitted.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/SelfSimilarCorollaries.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/SelfSimilarCorollaries.lean; bytes 2167..2643
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_SelfSimilarCorollaries_002

namespace OAI

universe uι

open scoped BigOperators ENNReal

namespace CorSetReference

variable {ι : Type uι} [Fintype ι] [Nonempty ι]

theorem cor_set {ι : Type uι} [Fintype ι] [Nonempty ι]
    (r t : ι → ℝ) (hr0 : ∀ i, 0 < |r i|) (hr1 : ∀ i, |r i| < 1)
    (hno : ∀ u v : List ι, u ≠ [] → v ≠ [] →
      word r t u = word r t v → u = v) :
    IsCompact (attractor r t) ∧ (attractor r t).Nonempty ∧
    (∃! s : ℝ, 0 ≤ s ∧ ∑ i, |r i| ^ s = 1) ∧
    (∀ s : ℝ, 0 ≤ s → (∑ i, |r i| ^ s = 1) →
      dimH (attractor r t) = ENNReal.ofReal (min 1 s)) := by
  sorry

end CorSetReference
end OAI
