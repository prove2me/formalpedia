-- Prove2me | Theorems.Thm_OAI_EuclideanRamsey_CircleConsequence_at_most_five_circle_points_ramsey
-- name    : OAI.EuclideanRamsey.CircleConsequence.at_most_five_circle_points_ramsey
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:32:38.197246+00:00
-- url     : https://prove2.me/theorems/9f5910df-9d61-4187-bc12-fdf0b2a0d8a3
-- statement:
--   The theorem states that, for a positive integer s ≤ 5 and an injective family a of s points in the Euclidean plane (Space 2, the real Euclidean space of dimension 2), if all the points lie on a common circle, meaning there exist a center c and a real radius r with dist(a i, c) = r for every i, then the configuration a is Ramsey. Here Ramsey means: for every number of colors r ≥ 2 there is a dimension D ≥ 1 such that for every coloring of Euclidean D-space with r colors there is a monochromatic congruent copy of a, that is, a family b of s points in that space with dist(b i, b j) = dist(a i, a j) for all i and j, and a single color k such that every b i has color k. In short, every nonempty set of at most five distinct concyclic points in the plane is Ramsey.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/EuclideanRamseyCircle.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/EuclideanRamseyCircle.lean; bytes 523..835
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_EuclideanRamseyCircle

namespace OAI

noncomputable section

namespace EuclideanRamsey

namespace CircleConsequence

/-- Every nonempty set of at most five distinct points on a circle is Ramsey. -/
theorem at_most_five_circle_points_ramsey {s : ℕ} (a : Fin s → Space 2)
    (hs : 0 < s) (hs5 : s ≤ 5) (ha : Function.Injective a)
    (hsphere : ∃ c : Space 2, ∃ r : ℝ, ∀ i, dist (a i) c = r) : Ramsey a := by
  sorry

end CircleConsequence
end EuclideanRamsey
end
end OAI
