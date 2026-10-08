-- Prove2me | Theorems.Thm_OAI_CannonRelease_cannon
-- name    : OAI.CannonRelease.cannon
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:32:25.972801+00:00
-- url     : https://prove2.me/theorems/13a0e91a-484a-40ad-a142-73a55b94b4bb
-- statement:
--   The theorem states an implication for a discrete group G with finite symmetric generating data D, meaning a finite set of generators closed under inversion whose Cayley graph is connected. Assume the Cayley graph has uniformly thin geodesic triangles: there is a natural number δ such that for any three group elements and any geodesic walks p, q, r (walks whose lengths equal the graph distances) forming a triangle, every vertex on p lies within graph distance δ of some vertex on q or r. Assume also that the boundary of D is homeomorphic to the 2-sphere in Euclidean 3-space. Here the boundary is the quotient of the space of based geodesic rays, namely maps r from the naturals to G with r(0)=1 and dist(r(i),r(j))=|i-j|, by the relation that two rays are equivalent when their distances at equal times n are bounded by a constant, with the quotient topology from the subspace topology of rays in sequences of G. Then there exists a group homomorphism ρ from G into the full isometry group of the upper-half-space model of hyperbolic 3-space, including orientation-reversing isometries, such that the action is proper (for every compact set K, only finitely many g have ρ(g)K meeting K), cocompact (some compact set K has translates under the image of G covering the whole space), and the kernel of ρ is a finite subset of G.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/CannonGeometricAction.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/CannonGeometricAction.lean; bytes 3563..3863
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_CannonGeometricAction

namespace OAI

noncomputable section

namespace CannonRelease

universe u

theorem cannon (G : Type u) [Group G] [TopologicalSpace G] [DiscreteTopology G]
    (D : CayleyData G) (hthin : D.ThinTriangles)
    (hsphere : Nonempty (Boundary D ≃ₜ SphereTwo)) :
    ∃ ρ : G →* H3Isom, ProperAction ρ ∧ CocompactAction ρ ∧
      (ρ.ker : Set G).Finite := by
  sorry

end CannonRelease
end
end OAI
