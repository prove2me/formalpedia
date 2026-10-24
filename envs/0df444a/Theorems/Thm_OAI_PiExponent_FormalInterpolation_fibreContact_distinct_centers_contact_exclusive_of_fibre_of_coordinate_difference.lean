-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_fibreContact_distinct_centers_contact_exclusive_of_fibre_of_coordinate_difference
-- name    : OAI.PiExponent.FormalInterpolation.fibreContact_distinct_centers_contact_exclusive_of_fibre_of_coordinate_difference
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T23:12:37.035512+00:00
-- url     : https://prove2.me/theorems/82311937-8885-4fdf-b51f-b364af6fc437
-- title:
--   A differing center coordinate excludes simultaneous positive contact
-- statement:
--   Given a coordinate where two center labels differ, the corresponding logarithmic coordinate evaluates, on the fibre x 0 = 1, to x i minus that center coordinate. Positive contact for both center ideals would force incompatible positive orders for these two evaluations, since their difference is a nonzero complex constant. The lemma packages the contact and valuation argument for one pair and one differing coordinate. Its hypotheses are consistent for m > 0; the separate zero-dimensional child handles m = 0.
-- source:
--   openai/math Approximation FibreNormalRigidity: nonconstant fibre coordinates imply quantitative contact bound.

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Definitions.Def_OAI_PiExponent_LogarithmicCenterIdeals
import Definitions.Def_OAI_PiExponent_FibreContactAuxiliaryData

open scoped BigOperators
open OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.fibreContact_distinct_centers_contact_exclusive_of_fibre_of_coordinate_difference
    {m K : Nat} (c : Fin K → Fin m → Complex)
    (hc : ∀ i : Fin m, Function.Injective (fun j : Fin K => c j i))
    (e : Fin (m + 1) → Nat) (he : ∀ i, 0 < e i)
    (E : Type) [Field E] [Algebra Complex E]
    (nu : PolynomialCurvePlace E) (x : Fin (m + 1) → E)
    (hfibre : x 0 = 1)
    (j k : Fin K) (hjk : j ≠ k)
    (hdiff : ∃ i : Fin m, c j i ≠ c k i) :
    ¬ (0 < polynomialCurveIdealContact nu x
          (logarithmicCenterIdeal (c j) (fun _ => e 0) e) ∧
       0 < polynomialCurveIdealContact nu x
          (logarithmicCenterIdeal (c k) (fun _ => e 0) e)) := by sorry
