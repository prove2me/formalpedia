-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_contact_mul_eq_sum
-- name    : OAI.PiExponent.FormalInterpolation.contact_mul_eq_sum
-- status  : Disproved
-- author  : @Eyal1990
-- created : 2026-10-24T09:16:17.49805+00:00
-- url     : https://prove2.me/theorems/e547c55d-83ad-40cd-8296-3faf66ca603a
-- title:
--   Contact of a finite ideal product is the sum of contacts
-- statement:
--   On the affine branch, contact of a finite product of ideals equals the sum of their contacts. This reduces the valuation argument to showing that the least attained finite order of a product ideal is the sum of the least attained finite orders of its factors, including the empty and zero-ideal cases.

import Definitions.Def_OAI_PiExponent_LogarithmicWordContact
import Definitions.Def_OAI_PiExponent_LogarithmicInterpolationNumerics
open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.contact_mul_eq_sum
    {K d : Nat} {E : Type} [Field E] [Algebra Complex E]
    (nu : PolynomialCurvePlace E) (x : Fin d → E)
    (I : Fin K → Ideal (MvPolynomial (Fin d) Complex))
    (hbranch : ∀ i, (0 : WithTop Int) ≤ nu.1 (x i)) :
    polynomialCurveIdealContact nu x (∏ j, I j) =
      ∑ j, polynomialCurveIdealContact nu x (I j) := by sorry
