-- Prove2me | Theorems.Thm_OAI_AbhyankarSathaye_exists_noncoordinate_polynomial
-- name    : OAI.AbhyankarSathaye.exists_noncoordinate_polynomial
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:32:20.381414+00:00
-- url     : https://prove2.me/theorems/2d385ca8-5074-4681-8bf0-87f7c3c71495
-- statement:
--   The theorem states that for every integer n ≥ 4, there exists a polynomial F in the complex polynomial ring ℂ[x₀, …, xₙ₋₁] such that its quotient by the principal ideal (F) is isomorphic, as a ℂ-algebra, to the polynomial ring in n − 1 variables, while F is not a coordinate of the original polynomial ring. Explicitly, no ℂ-algebra automorphism of ℂ[x₀, …, xₙ₋₁] sends any variable xᵢ to F. Thus the hypersurface defined by F has the coordinate ring of complex affine (n − 1)-space even though no polynomial change of coordinates in the ambient n-dimensional affine space makes F one of its coordinate functions.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/AbhyankarSathaye.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/AbhyankarSathaye.lean; bytes 176..692
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations

namespace OAI

namespace AbhyankarSathaye

/-- In every dimension at least four, a polynomial can define affine space
without being a coordinate of the ambient polynomial ring. -/
theorem exists_noncoordinate_polynomial (n : ℕ) (hn : 4 ≤ n) :
    ∃ F : MvPolynomial (Fin n) ℂ,
      Nonempty ((MvPolynomial (Fin n) ℂ ⧸ Ideal.span {F}) ≃ₐ[ℂ]
        MvPolynomial (Fin (n - 1)) ℂ) ∧
      ¬ ∃ (equiv : MvPolynomial (Fin n) ℂ ≃ₐ[ℂ] MvPolynomial (Fin n) ℂ)
        (index : Fin n), equiv (MvPolynomial.X index) = F := by
  sorry

end AbhyankarSathaye
end OAI
