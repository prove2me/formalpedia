-- Prove2me | Theorems.Thm_OAI_SymmetricMahler_symmetric_mahler_equality
-- name    : OAI.SymmetricMahler.symmetric_mahler_equality
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:33:28.154341+00:00
-- url     : https://prove2.me/theorems/e8590143-c84b-4568-b38c-67c4357ea7ba
-- statement:
--   The theorem is stated without a proof (admitted). It says that for n ≥ 1 and a compact, convex, origin-symmetric subset K of ℝⁿ (x ∈ K implies −x ∈ K) with nonempty interior, the product of the volumes (Lebesgue measure, taken as real numbers) of K and of its coordinate polar equals 4ⁿ/n! if and only if K is a linear Hanner body. The coordinate polar of K is the set of vectors p with Σᵢ pᵢvᵢ ≤ 1 for every v in K. A set is Hanner if it is built recursively from intervals [−a, a] in one dimension with a > 0, using two operations: the product of Hanner sets A ⊆ ℝᵏ and B ⊆ ℝˡ, namely all concatenations (x, y) with x in A and y in B, and the join, namely the convex hull of the union of A embedded as (x, 0) and B embedded as (0, y) in ℝᵏ⁺ˡ. K is a linear Hanner body if K = T(H) for some Hanner set H in ℝⁿ and some invertible linear map T of ℝⁿ.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/SymmetricMahlerEquality.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/SymmetricMahlerEquality.lean; bytes 1353..1694
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_SymmetricMahlerEquality

namespace OAI

namespace SymmetricMahler

noncomputable section

open Set MeasureTheory Metric

theorem symmetric_mahler_equality {n : ℕ} (hn : 1 ≤ n)
    {K : Set (Fin n → ℝ)} (hK : IsCompact K) (hconv : Convex ℝ K)
    (hsym : ∀ x ∈ K, -x ∈ K) (hint : (interior K).Nonempty) :
    ((volume K).toReal * (volume (coordinatePolar K)).toReal =
      (4 : ℝ)^n / (Nat.factorial n : ℝ)) ↔ IsLinearHanner K := by
  sorry

end
end SymmetricMahler
end OAI
