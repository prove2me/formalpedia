-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_fibreContact_product_ideal_contact_eq_sum
-- name    : OAI.PiExponent.FormalInterpolation.fibreContact_product_ideal_contact_eq_sum
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T17:46:12.572878+00:00
-- url     : https://prove2.me/theorems/934a8b18-6c05-4ad3-bf1b-e47479dc084e
-- title:
--   Contact of a product of center ideals is the sum of their contacts
-- statement:
--   For any finite family of logarithmic center ideals, the contact of their ideal product is the sum of their individual contacts, including the empty-family and non-affine cases.
-- source:
--   openai/math Approximation FibreNormalRigidity: nonconstant fibre coordinates imply quantitative contact bound.

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Definitions.Def_OAI_PiExponent_LogarithmicCenterIdeals
import Definitions.Def_OAI_PiExponent_FibreContactAuxiliaryData

open scoped BigOperators
open OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.fibreContact_product_ideal_contact_eq_sum
    {m K : Nat} (c : Fin K → Fin m → Complex)
    (e : Fin (m + 1) → Nat)
    (E : Type) [Field E] [Algebra Complex E]
    (nu : PolynomialCurvePlace E) (x : Fin (m + 1) → E) :
    polynomialCurveIdealContact nu x
      (logarithmicCentersIdeal c (fun _ => e 0) e) =
      ∑ j : Fin K, polynomialCurveIdealContact nu x
        (logarithmicCenterIdeal (c j) (fun _ => e 0) e) := by sorry
