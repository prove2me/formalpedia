-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_constant_fibre_contact_localization_matched
-- name    : OAI.PiExponent.FormalInterpolation.constant_fibre_contact_localization_matched
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-21T03:52:59.83873+00:00
-- url     : https://prove2.me/theorems/3b3475c1-b558-4f0f-ad39-cb056d4bcfb2
-- title:
--   Contact bound from a matching center’s coordinate divisor
-- statement:
--   When `j` matches at `i0`, use its `k`-coordinate generator and the `i0` generators for all other centers. Injectivity and the matching equality make the latter factors nonzero constants after evaluation. The resulting product gives the contact bound by the positive order of the matching coordinate divisor, multiplied by `e k.succ`. This isolates the matched branch; the ideal membership, order comparison, and finite-support summation remain to be proved. An independent route is to establish the product’s membership in the product ideal, compare its valuation with the defining `sInf` at affine places, handle the off-affine zero case, and then sum using support containment in the divisor of `x k.succ − c j k`. The hypothesis `hk` ensures this divisor function is nonzero; zero exponent yields order zero.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Definitions.Def_OAI_PiExponent_LogarithmicInterpolationNumerics
import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Mathlib.RingTheory.Algebraic.Defs

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.constant_fibre_contact_localization_matched
    {m K : Nat} (c : Fin K → Fin m → Complex)
    (hc : ∀ i : Fin m, Function.Injective (fun j : Fin K => c j i))
    (T : Fin m → Nat) (e : Fin (m + 1) → Nat)
    (E : Type) [Field E] [Algebra Complex E] [Algebra.EssFiniteType Complex E]
    (htrdeg : Algebra.trdeg Complex E = 1) (x : Fin (m + 1) → E)
    (hgen : IntermediateField.adjoin Complex (Set.range x) = ⊤)
    (hfibre : x 0 = 1)
    (i0 : Fin m) (a : Complex) (ha : x i0.succ = algebraMap Complex E a)
    (k : Fin m) (hk : Transcendental Complex (x k.succ))
    (j : Fin K) (hj : c j i0 = a) :
    (∑ᶠ nu : PolynomialCurvePlace E,
      (polynomialCurveIdealContact nu x (logarithmicCentersIdeal c T e) : Real)) ≤
      (e k.succ : Real) *
        ∑ᶠ nu : PolynomialCurvePlace E,
          max (polynomialCurveOrder nu
            (x k.succ - algebraMap Complex E (c j k)) : Real) 0 := by sorry
