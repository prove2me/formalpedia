-- Prove2me | Theorems.Thm_OAI_CoveringOrder_optimal_order
-- name    : OAI.CoveringOrder.optimal_order
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:32:30.064686+00:00
-- url     : https://prove2.me/theorems/6e54982b-b43b-4c7f-bb0f-1e2b52a90bc6
-- statement:
--   The theorem states that the proposition OptimalOrder holds, i.e. there exist real constants c>0 and C>0 and a threshold n₀ such that for every dimension n≥n₀ four extremal covering-density quantities each lie, as extended nonnegative reals, between c·n·log n and C·n·log n (so each is in particular finite). The quantities are suprema over convex bodies in n-dimensional Euclidean space, where a convex body is a compact convex set with nonempty interior. The first is the supremum over all convex bodies K of the translative covering density thetaT(K), the infimum of vol(K) times the upper center intensity over locally finite center sets X for which the translates K+x, x in X, cover the space; the upper center intensity is the limsup as R→∞ of the number of centers in the cube [−R,R]^n divided by (2R)^n. The second is the same supremum restricted to centrally symmetric convex bodies, meaning those satisfying x∈K iff 2z−x∈K for some center z. The third is the supremum over all convex bodies of the lattice covering density thetaL(K), the infimum over discrete full-rank lattices Λ with Λ+K covering the space of vol(K) divided by the covolume of Λ. The fourth is that lattice supremum restricted to centrally symmetric convex bodies.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/CoveringDensity.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/CoveringDensity.lean; bytes 4134..4360
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_CoveringDensity

namespace OAI

/-- Translative and lattice covering densities over all convex bodies and over
centrally symmetric convex bodies have the same asymptotic order. -/
theorem CoveringOrder.optimal_order : CoveringOrder.OptimalOrder := by
  sorry

end OAI
