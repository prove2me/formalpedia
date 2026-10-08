-- Prove2me | Theorems.Thm_OAI_MUB6_fourier_and_family_bound
-- name    : OAI.MUB6.fourier_and_family_bound
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:32:54.543566+00:00
-- url     : https://prove2.me/theorems/d35da01b-615f-480f-9b76-4c7c16c14ffe
-- statement:
--   The theorem states a conjunction of two claims about 6x6 complex matrices and mutually unbiased bases in C^6. First, for every complex Hadamard matrix H of order 6 (all entries of modulus 1 and H*H = 6I, where H* is the conjugate transpose) that is not equivalent to the specific matrix tao, every permutation π of the six coordinates gives g(H, alpha∘π) = 0. Here the character of a column x at an integer exponent vector a is the product over i of x_i^{a_i}, g(H,a) is (1/6) times the sum over the six columns k of H of the character of column k at a, and alpha is the exponent vector (1,1,1,-1,-1,-1), so alpha∘π is alpha with its entries permuted. Equivalence of H and K means K_{ij} = u_i H_{r(i),c(j)} v_j for some row and column permutations r, c and unit-modulus complex phase vectors u and v. The matrix tao has entries ω^{e_{ij}}, where ω = exp(2πi/3) and e is a fixed 6x6 exponent matrix with zero first row and column and a five-cycle pattern of exponents 0, 1, 2 in the remaining 5x5 block. Second, for every natural number n, if there exist n orthonormal bases of C^6 that are pairwise mutually unbiased, meaning |<b_i, b'_j>|^2 = 1/6 for all vectors of two distinct bases, then n ≤ 5. This is stated as an admitted theorem, not a verified proof.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/MUBSix.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/MUBSix.lean; bytes 1674..1899
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_MUBSix

namespace OAI

noncomputable section

open scoped BigOperators ComplexConjugate

namespace MUB6

theorem fourier_and_family_bound :
    (∀ H : CMatrix, IsHadamard H → ¬Equivalent H tao →
      ∀ π : Equiv.Perm Coord, g H (permuteCharge π alpha) = 0) ∧
    (∀ n : ℕ, Attainable n → n ≤ 5) := by
  sorry

end MUB6
end
end OAI
