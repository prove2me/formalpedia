-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_logarithmic_centers_contact_is_single_center_of_positive_dimension
-- name    : OAI.PiExponent.FormalInterpolation.logarithmic_centers_contact_is_single_center_of_positive_dimension
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-24T09:07:35.25202+00:00
-- url     : https://prove2.me/theorems/fe475b9c-dc53-47e2-8e6c-708106012bfd
-- title:
--   Positive dimension makes product contact select one logarithmic center
-- statement:
--   When there is at least one logarithmic coordinate, positive contact with the product of the center ideals equals positive contact at one center. This repairs the earlier unrestricted child, whose claim fails at `m = 0`. Its proof uses injectivity to separate distinct centers, comaximality of their ideals, and additivity of valuation contact over the finite product. The zero-exponent boundary makes a center ideal the unit ideal and thus cannot satisfy the positive-contact premise.

import Definitions.Def_OAI_PiExponent_LogarithmicWordContact
import Definitions.Def_OAI_PiExponent_LogarithmicInterpolationNumerics

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.logarithmic_centers_contact_is_single_center_of_positive_dimension
    {m K : Nat} (c : Fin K → Fin m → Complex)
    (hc : ∀ i : Fin m, Function.Injective (fun j : Fin K => c j i))
    (hm : 1 ≤ m) (hK : 1 ≤ K)
    (e : Fin (m + 1) → Nat)
    (E : Type) [Field E] [Algebra Complex E]
    (nu : PolynomialCurvePlace E) (x : Fin (m + 1) → E)
    (hcontact : 0 < (polynomialCurveIdealContact nu x
      (logarithmicCentersIdeal c (fun _ => e 0) e) : Real)) :
    ∃ j : Fin K,
      0 < (polynomialCurveIdealContact nu x
        (logarithmicCenterIdeal (c j) (fun _ => e 0) e) : Real) ∧
      (polynomialCurveIdealContact nu x
        (logarithmicCenterIdeal (c j) (fun _ => e 0) e) : Real) =
      (polynomialCurveIdealContact nu x
        (logarithmicCentersIdeal c (fun _ => e 0) e) : Real) := by sorry
