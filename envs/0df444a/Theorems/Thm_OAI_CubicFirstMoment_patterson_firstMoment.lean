-- Prove2me | Theorems.Thm_OAI_CubicFirstMoment_patterson_firstMoment
-- name    : OAI.CubicFirstMoment.patterson_firstMoment
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:32:31.857053+00:00
-- url     : https://prove2.me/theorems/bf2acce9-e4c5-4df9-a66d-e364d23cfeb9
-- statement:
--   The theorem states that, working in the Eisenstein integers Z[ω] with ω = exp(2πi/3), the sum over all primary Eisenstein primes p of norm N(p) = |p|² at most X of the normalized cubic Gauss sum g(p) equals (6/5)·c*·X^(5/6)/log X up to an error that is o(X^(5/6)/log X) as X tends to infinity, where c* = (2π)^(2/3)/(3Γ(2/3)). Here an element p is primary when 3 divides p − 1, and a primary prime is a primary element that is prime in Z[ω]. The Gauss sum g(p) is N(p)^(-1/2) times the sum, over residue classes v modulo p (using a chosen representative of each class), of the cubic residue symbol of v at p multiplied by the additive phase exp(2πi(z + z̄)) with z = v/p. The cubic symbol is 0 when v is not a unit modulo p; otherwise it is ω^j, where j in {0,1,2} is the index with v^((N(p)−1)/3) congruent to ω^j modulo p, and it is 0 if no such j exists. The statement is the defined proposition FirstMomentStatement, asserted here as an admitted theorem.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/PattersonFirstMoment.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/PattersonFirstMoment.lean; bytes 2772..2904
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

/-- The sharp first moment over all primary Eisenstein primes. -/
theorem patterson_firstMoment : FirstMomentStatement := by
  sorry

end CubicFirstMoment
end
end
end OAI
