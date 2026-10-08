-- Prove2me | Theorems.Thm_OAI_SignedDisk_CenteredDiskEndpoint_main_signed_finite_band
-- name    : OAI.SignedDisk.CenteredDiskEndpoint.main_signed_finite_band
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:33:21.579251+00:00
-- url     : https://prove2.me/theorems/c881525c-8981-44f0-9fea-d43f4fb565bb
-- statement:
--   The theorem states that the defined proposition SignedFiniteBandStatement holds (the proof is admitted, not verified). On the Euclidean plane ℝ², write diskAverage(f,x,r) for the integral of f over the open ball B(x,r) divided by πr², and signedBand(f,a,b)(x) for the supremum of diskAverage(f,x,r) over all real r in the closed interval [a,b], endpoints included, with no absolute value taken. The statement asserts that there is a constant C ≥ 0 such that for every smooth (C^∞) compactly supported f : ℝ² → ℝ, every a > 0 and every natural number m, the function signedBand(f,a,2^m a) is locally integrable and has an integrable vector-valued weak gradient G : ℝ² → ℝ². Weak gradient means that for every smooth compactly supported test function φ and each coordinate i, ∫ signedBand·∂ᵢφ = −∫ Gᵢ φ. Moreover the L¹ norm of G, ∫‖G‖ with the Euclidean norm, is at most C times the L¹ norm of the gradient of f. The constant C does not depend on f, a or m.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/SignedFiniteBand.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/SignedFiniteBand.lean; bytes 1623..1696
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_SignedFiniteBand

namespace OAI

noncomputable section

namespace SignedDisk

open MeasureTheory Set

open scoped ENNReal NNReal Topology ContDiff

namespace CenteredDiskEndpoint

theorem main_signed_finite_band : SignedFiniteBandStatement := by
  sorry

end CenteredDiskEndpoint
end SignedDisk
end
end OAI
