-- Prove2me | Theorems.Thm_OAI_CubicFirstMoment_patterson_angularCancellation
-- name    : OAI.CubicFirstMoment.patterson_angularCancellation
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:32:31.571914+00:00
-- url     : https://prove2.me/theorems/18f8d27a-f886-4f23-8df6-2f04534f84eb
-- statement:
--   The theorem states that, for every nonzero integer ℓ, the angularly twisted prime sum of normalized cubic Gauss sums is of smaller order than the first-moment scale. Here the Eisenstein integers are the subring of ℂ generated over ℤ by ω = exp(2πi/3), the norm N(a) is |a|², a primary prime is a prime element p of this ring with p ≡ 1 modulo 3, and gaussAtPrime(p) is N(p)^(-1/2) times the sum over residue classes v modulo p of the cubic residue symbol at p (the cube root of unity ω^j with v^((N(p)-1)/3) ≡ ω^j mod p when v is a unit mod p, and 0 otherwise) multiplied by the additive phase exp(2πi(z + z̄)) with z = v/p. The angular character is θ_ℓ(p) = (p/|p|)^ℓ, and the cutoff sum is the sum of θ_ℓ(p)·gaussAtPrime(p) over primary primes p with N(p) ≤ X. The claim is that this sum is o(X^(5/6)/log X) as X → ∞ for each ℓ ≠ 0, so no first-moment-size contribution survives in any nonzero angular mode.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/PattersonFirstMoment.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/PattersonFirstMoment.lean; bytes 3047..3206
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_PattersonFirstMoment

namespace OAI

section

noncomputable section

open scoped BigOperators

open Module

attribute [local instance] Classical.propDecidable

namespace CubicFirstMoment

/-- Cancellation at the first-moment scale for each nonzero angular mode. -/
theorem patterson_angularCancellation : AngularCancellationStatement := by
  sorry

end CubicFirstMoment
end
end
end OAI
