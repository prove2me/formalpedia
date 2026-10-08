-- Prove2me | Theorems.Thm_OAI_PerfectMatchingPSD_affine_lift_lower_bound
-- name    : OAI.PerfectMatchingPSD.affine_lift_lower_bound
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:33:02.221268+00:00
-- url     : https://prove2.me/theorems/c60016c3-87f9-4168-a0e4-7149a740fcb8
-- statement:
--   The theorem states that the positive-semidefinite lift size of the perfect matching polytope on an even number n of vertices grows faster than any polynomial in n. Here an edge is a pair (a,b) of elements of Fin n with a<b, a perfect matching is a set of edges in which every vertex lies in exactly one edge, and the matching polytope is the convex hull in the real vector space of functions on edges of the 0/1 indicator vectors of all perfect matchings. HasAffineLift(n,r) means that there exist an affine subspace L of the real r×r matrices and an affine map T from r×r real matrices to functions on edges such that the image under T of the set of positive semidefinite matrices lying in L equals the matching polytope. Formally, for every real C>0 there exists n₀ with n₀ ≥ 4 such that for every n ≥ n₀ with n even and every natural number r for which HasAffineLift(n,r) holds, we have n^C < r. The theorem is stated with a proof placeholder in the source.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/MatchingAffineLift.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/MatchingAffineLift.lean; bytes 841..1060
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_MatchingAffineLift

namespace OAI

namespace PerfectMatchingPSD

theorem affine_lift_lower_bound :
    ∀ C : ℝ, 0 < C → ∃ n₀ : ℕ, 4 ≤ n₀ ∧
      ∀ n : ℕ, n₀ ≤ n → Even n → ∀ r : ℕ,
        HasAffineLift n r → (n : ℝ) ^ C < (r : ℝ) := by
  sorry

end PerfectMatchingPSD
end OAI
