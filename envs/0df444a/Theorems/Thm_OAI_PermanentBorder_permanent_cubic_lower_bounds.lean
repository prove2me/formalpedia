-- Prove2me | Theorems.Thm_OAI_PermanentBorder_permanent_cubic_lower_bounds
-- name    : OAI.PermanentBorder.permanent_cubic_lower_bounds
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:33:02.786855+00:00
-- url     : https://prove2.me/theorems/008afcd3-f398-4dad-b145-1dfab68a3835
-- statement:
--   The theorem states two lower bounds on the size of determinantal representations of the m×m permanent. Here permanentPolynomial(m) is the complex polynomial in the m² variables X(i,j), equal to the sum over all permutations τ of {0,…,m−1} of the product over i of X(i,τ(i)). An exact determinant representation of size n means n>0 and there exist complex n×n matrices A₀ and A_v, one for each variable v, such that the determinant of the matrix A₀ + Σ_v v·A_v (an affine matrix of polynomials) equals the polynomial identically. A border determinant representation of size n means n>0 and there are sequences of such matrices A₀(j), A_v(j), indexed by natural numbers j, such that for every monomial exponent d, the coefficient of d in the determinant of the j-th affine matrix converges to the coefficient of d in the polynomial as j→∞. The theorem asserts that for every m ≥ 1408 and every n, if the permanent of size m has a border determinant representation of size n, then n ≥ m³/(5529600·e), where e is Euler's number, and likewise, with the same bound, if it has an exact determinant representation of size n.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/PermanentCubic.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/PermanentCubic.lean; bytes 1169..1516
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_PermanentCubic

namespace OAI

namespace PermanentBorder

open Filter

open scoped Topology

theorem permanent_cubic_lower_bounds :
    (∀ (m n : ℕ), 1408 ≤ m → HasBorderDeterminant n (permanentPolynomial m) →
      (m : ℝ)^3 / (5529600 * Real.exp 1) ≤ (n : ℝ)) ∧
    (∀ (m n : ℕ), 1408 ≤ m → HasExactDeterminant n (permanentPolynomial m) →
      (m : ℝ)^3 / (5529600 * Real.exp 1) ≤ (n : ℝ)) := by
  sorry

end PermanentBorder
end OAI
