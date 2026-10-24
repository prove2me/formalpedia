-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_fibreContact_distinct_centers_contact_exclusive
-- name    : OAI.PiExponent.FormalInterpolation.fibreContact_distinct_centers_contact_exclusive
-- status  : Disproved
-- author  : @Eyal1990
-- created : 2026-10-23T17:46:29.549475+00:00
-- url     : https://prove2.me/theorems/4df5299f-c67c-44f9-a782-b6828f8ec94e
-- title:
--   Distinct centers cannot both have positive contact
-- statement:
--   Under coordinatewise injectivity of the centers and positive generator exponents, at most one center ideal can have positive contact at a given place.
-- source:
--   openai/math Approximation FibreNormalRigidity: nonconstant fibre coordinates imply quantitative contact bound.

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Definitions.Def_OAI_PiExponent_LogarithmicCenterIdeals
import Definitions.Def_OAI_PiExponent_FibreContactAuxiliaryData

open scoped BigOperators
open OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.fibreContact_distinct_centers_contact_exclusive
    {m K : Nat} (c : Fin K → Fin m → Complex)
    (hc : ∀ i : Fin m, Function.Injective (fun j : Fin K => c j i))
    (e : Fin (m + 1) → Nat) (he : ∀ i, 0 < e i)
    (E : Type) [Field E] [Algebra Complex E]
    (nu : PolynomialCurvePlace E) (x : Fin (m + 1) → E) :
    ∀ j k : Fin K, j ≠ k →
      ¬ (0 < polynomialCurveIdealContact nu x
            (logarithmicCenterIdeal (c j) (fun _ => e 0) e) ∧
         0 < polynomialCurveIdealContact nu x
            (logarithmicCenterIdeal (c k) (fun _ => e 0) e)) := by sorry
