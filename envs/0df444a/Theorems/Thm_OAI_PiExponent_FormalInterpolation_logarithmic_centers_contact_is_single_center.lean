-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_logarithmic_centers_contact_is_single_center
-- name    : OAI.PiExponent.FormalInterpolation.logarithmic_centers_contact_is_single_center
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-21T09:15:27.68405+00:00
-- url     : https://prove2.me/theorems/d1cc489f-e0d6-4f6a-a342-275cc9a428d8
-- title:
--   Positive product contact selects one logarithmic center
-- statement:
--   Positive contact with the product of the logarithmic center ideals is equal to the positive contact at one of its centers. This removes the product-ideal case distinction from the parent. A proof can establish that distinct centers give comaximal ideals at an affine branch using coordinatewise injectivity, then use additivity of valuation contact for products. The statement is meaningful also when `K = 1`; if `m = 0`, the injectivity hypothesis rules out multiple centers.

import Definitions.Def_OAI_PiExponent_LogarithmicWordContact
import Definitions.Def_OAI_PiExponent_LogarithmicInterpolationNumerics

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.logarithmic_centers_contact_is_single_center
    {m K : Nat} (c : Fin K → Fin m → Complex)
    (hc : ∀ i : Fin m, Function.Injective (fun j : Fin K => c j i))
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
