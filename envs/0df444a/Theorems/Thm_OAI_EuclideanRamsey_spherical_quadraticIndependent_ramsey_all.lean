-- Prove2me | Theorems.Thm_OAI_EuclideanRamsey_spherical_quadraticIndependent_ramsey_all
-- name    : OAI.EuclideanRamsey.spherical_quadraticIndependent_ramsey_all
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:32:38.986592+00:00
-- url     : https://prove2.me/theorems/5de84265-acd2-4d01-9f9e-884eb1e7d7dd
-- statement:
--   The theorem states that, for natural numbers s and d, a family a of s points a_0,...,a_{s-1} in d-dimensional Euclidean space ℝ^d has the Ramsey property whenever four hypotheses hold: the map i ↦ a_i is injective; the affine span of the points is all of ℝ^d; the points are spherical, meaning there exist a center c and radius r with dist(a_i,c)=r for every i; and a quadratic independence condition holds. Let K be the subfield of ℝ generated over ℚ by all coordinates of all the points. For each i, form the vector (1, a_i1, ..., a_id), indexed by Option (Fin d), with first entry 1. The condition says that the s vectors in the space of K-valued functions on pairs (p,q) of indices from Option (Fin d), given by (p,q) ↦ (entry p of vector i)·(entry q of vector i), are linearly independent over K. Ramsey(a) means that for every r ≥ 2 there is a dimension D ≥ 1 such that every r-coloring of ℝ^D admits a congruent copy b of the family, that is, dist(b_i,b_j)=dist(a_i,a_j) for all i,j, with all points b_i the same color.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/EuclideanRamseyQuadratic.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/EuclideanRamseyQuadratic.lean; bytes 1050..1468
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_EuclideanRamseyQuadratic

namespace OAI

noncomputable section

namespace EuclideanRamsey

theorem spherical_quadraticIndependent_ramsey_all {s d : ℕ}
    (a : Fin s → Space d) (ha : Function.Injective a)
    (hspan : affineSpan ℝ (Set.range a) = ⊤)
    (hsphere : ∃ c : Space d, ∃ r : ℝ, ∀ i, dist (a i) c = r)
    (hrows : LinearIndependent (Coeff a)
      (fun i : Fin s => fun q : Option (Fin d) × Option (Fin d) =>
        augmented a i q.1 * augmented a i q.2)) : Ramsey a := by
  sorry

end EuclideanRamsey
end
end OAI
