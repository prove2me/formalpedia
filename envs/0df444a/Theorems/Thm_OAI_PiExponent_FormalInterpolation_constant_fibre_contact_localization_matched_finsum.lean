-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_constant_fibre_contact_localization_matched_finsum
-- name    : OAI.PiExponent.FormalInterpolation.constant_fibre_contact_localization_matched_finsum
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-21T04:01:53.324733+00:00
-- url     : https://prove2.me/theorems/857c7a7f-ae0e-4447-9fb1-a50c1ef30af6
-- title:
--   Sum a pointwise contact bound over the coordinate divisor
-- statement:
--   Given the pointwise contact bound, establish the finite-support summation inequality, accounting for the divisor support and the off-affine zero-contact convention.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Definitions.Def_OAI_PiExponent_LogarithmicInterpolationNumerics
import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Mathlib.RingTheory.Algebraic.Defs

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.constant_fibre_contact_localization_matched_finsum
    {m K : Nat} (c : Fin K → Fin m → Complex)
    (hc : ∀ i : Fin m, Function.Injective (fun j : Fin K => c j i))
    (T : Fin m → Nat) (e : Fin (m + 1) → Nat)
    (E : Type) [Field E] [Algebra Complex E] [Algebra.EssFiniteType Complex E]
    (htrdeg : Algebra.trdeg Complex E = 1) (x : Fin (m + 1) → E)
    (hgen : IntermediateField.adjoin Complex (Set.range x) = ⊤)
    (hfibre : x 0 = 1)
    (i0 : Fin m) (a : Complex) (ha : x i0.succ = algebraMap Complex E a)
    (k : Fin m) (hk : Transcendental Complex (x k.succ))
    (j : Fin K) (hj : c j i0 = a)
    (hlocal : ∀ nu : PolynomialCurvePlace E,
      (polynomialCurveIdealContact nu x (logarithmicCentersIdeal c T e) : Real) ≤
        (e k.succ : Real) *
          max (polynomialCurveOrder nu
            (x k.succ - algebraMap Complex E (c j k)) : Real) 0) :
    (∑ᶠ nu : PolynomialCurvePlace E,
      (polynomialCurveIdealContact nu x (logarithmicCentersIdeal c T e) : Real)) ≤
      (e k.succ : Real) *
        ∑ᶠ nu : PolynomialCurvePlace E,
          max (polynomialCurveOrder nu
            (x k.succ - algebraMap Complex E (c j k)) : Real) 0 := by sorry
