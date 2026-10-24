-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_fibreContact_zero_dimensional_contact_vanishes
-- name    : OAI.PiExponent.FormalInterpolation.fibreContact_zero_dimensional_contact_vanishes
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T23:12:18.425689+00:00
-- url     : https://prove2.me/theorems/72eadd7b-5d89-4ec9-b3f8-09d06059b932
-- title:
--   The zero-dimensional fibre generator has zero contact
-- statement:
--   For m = 0, the logarithmic center ideal is generated only by a positive power of X 0 − 1. Under x 0 = 1 that generator evaluates to zero, so its ideal has contact zero. This handles all j and k, including the vacuous label cases.
-- source:
--   openai/math Approximation FibreNormalRigidity: nonconstant fibre coordinates imply quantitative contact bound.

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Definitions.Def_OAI_PiExponent_LogarithmicCenterIdeals
import Definitions.Def_OAI_PiExponent_FibreContactAuxiliaryData

open scoped BigOperators
open OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.fibreContact_zero_dimensional_contact_vanishes
    {K : Nat} (c : Fin K → Fin 0 → Complex)
    (e : Fin 1 → Nat) (he : ∀ i, 0 < e i)
    (E : Type) [Field E] [Algebra Complex E]
    (nu : PolynomialCurvePlace E) (x : Fin 1 → E)
    (hfibre : x 0 = 1) :
    ∀ j k : Fin K, j ≠ k →
      ¬ (0 < polynomialCurveIdealContact nu x
            (logarithmicCenterIdeal (c j) (fun _ => e 0) e) ∧
         0 < polynomialCurveIdealContact nu x
            (logarithmicCenterIdeal (c k) (fun _ => e 0) e)) := by sorry
