-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_contact_product_eq_sum_of_affine_contacts
-- name    : OAI.PiExponent.FormalInterpolation.contact_product_eq_sum_of_affine_contacts
-- status  : Disproved
-- author  : @Eyal1990
-- created : 2026-10-24T09:26:26.393181+00:00
-- url     : https://prove2.me/theorems/411de64d-954f-4c42-b793-f6153e6fa85e
-- title:
--   Contact of an affine finite ideal product is the sum of factor contacts
-- statement:
--   On the affine branch, contact of a finite product of ideals equals the sum of factor contacts, including the empty-family and zero-contact cases. This isolates the minimum-valuation and ideal-product argument from the parent. Prove it by characterizing contact as the least attained finite valuation order: every product contribution has order at least the sum of the two minima, while multiplying elements attaining those minima realizes the sum. Handle an empty attained-order set separately, where the ideal and product contacts are zero.

import Definitions.Def_OAI_PiExponent_LogarithmicWordContact
import Definitions.Def_OAI_PiExponent_LogarithmicInterpolationNumerics
open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.contact_product_eq_sum_of_affine_contacts
    {K d : Nat} {E : Type} [Field E] [Algebra Complex E]
    (nu : PolynomialCurvePlace E) (x : Fin d → E)
    (I : Fin K → Ideal (MvPolynomial (Fin d) Complex))
    (hbranch : ∀ i, (0 : WithTop Int) ≤ nu.1 (x i)) :
    polynomialCurveIdealContact nu x (∏ j, I j) =
      ∑ j, polynomialCurveIdealContact nu x (I j) := by sorry
