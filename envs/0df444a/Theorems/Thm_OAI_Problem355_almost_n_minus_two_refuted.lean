-- Prove2me | Theorems.Thm_OAI_Problem355_almost_n_minus_two_refuted
-- name    : OAI.Problem355.almost_n_minus_two_refuted
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:33:10.845806+00:00
-- url     : https://prove2.me/theorems/3e13c402-91b1-471a-800b-1859458670fc
-- statement:
--   The theorem states that, with ε* = heilbronnExponent = 1/(100000·K), where K = T²+1, T = C(M,3) and M = C(4·41−1, 41) = C(163,41) (a fixed explicit positive constant), the number ε*/2 is positive, and the following eventual almost-upper-bound property fails for ε = ε*/2. That property, eventualAlmostUpperBound(ε), asserts the existence of a real C>0 and a natural number n₀ such that for every n ≥ n₀ with n ≥ 3 and every set P of exactly n points of the unit square [0,1]×[0,1], some three distinct points of P span a triangle of area at most C·n^(−2+ε). So the theorem asserts that no such constant C and threshold n₀ exist for ε = ε*/2, that is, for every C>0 and n₀ there are some n ≥ max(n₀,3) and an n-point subset of the unit square in which all triangles formed by distinct points have area greater than C·n^(−2+ε*/2). The statement is admitted in the source rather than proved here.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/HeilbronnTriangle.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/HeilbronnTriangle.lean; bytes 1826..1968
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_HeilbronnTriangle

namespace OAI

noncomputable section

namespace Problem355

attribute [local irreducible] Problem355.heilbronnT
  Problem355.heilbronnM

theorem almost_n_minus_two_refuted :
    0 < heilbronnExponent / 2 ∧
      ¬ eventualAlmostUpperBound (heilbronnExponent / 2) := by
  sorry

end Problem355
end
end OAI
