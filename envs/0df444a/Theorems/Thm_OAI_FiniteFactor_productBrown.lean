-- Prove2me | Theorems.Thm_OAI_FiniteFactor_productBrown
-- name    : OAI.FiniteFactor.productBrown
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:32:40.934444+00:00
-- url     : https://prove2.me/theorems/29d60677-2d88-46f2-9d2d-8660a91048ab
-- statement:
--   The theorem states that the defined proposition ProductBrownClaim holds. The setting is the Hilbert space L² of the product measure on (ℝ^I)×ℤ, where I is the countable coordinate set of pairs (s,j) with s a natural number and 0≤j<m_s for a stage-dependent block size m_s, ℝ^I carries the infinite product of Lebesgue measure restricted to [0,1), and ℤ carries counting measure. For a family θ of real angles indexed by I, with weights c_i given by a stage constant C_s depending only on the block index s (nonnegative), the operator is the composition of a bilateral shift (z,k)↦(z,k−1) with multiplication by a diagonal function equal to exp(−Σ_i c_i·⌊x_i+θ_i⌋) evaluated at the rotated point whose coordinates are the fractional parts of x_i+kθ_i; this function is bounded by 1 when θ and c are nonnegative. SourceAngles(θ) requires, for every coordinate (s,j), that 1/(m_s·K_s) ≤ θ_(s,j) ≤ 2/(m_s·K_s), where K_s is a stage cutoff. The vacuum functional sends an operator T to the inner product of the vacuum vector, the indicator function of the slice at integer level 0, with T applied to it. The claim says that for every angle family θ satisfying SourceAngles, the point mass at 0 in ℂ is a Brown measure of this operator relative to the vacuum functional: it is a compact-support probability measure, and for every complex z, the Fuglede–Kadison determinant of T−z, defined as the infimum over n of exp of the real part of the vacuum functional applied to the functional calculus of log(max(e^{−n},·)) at |T−z|, equals the infimum over n of exp(∫ log(max(e^{−n},|z−w|)) dμ(w)) with μ the point mass at 0.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/ProductBrown.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/ProductBrown.lean; bytes 32738..32874
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_ProductBrown

namespace OAI

namespace FiniteFactor

/-- The Brown measure of the product weighted shift is the point mass at zero. -/
theorem productBrown : ProductBrownClaim := by
  sorry

end FiniteFactor
end OAI
