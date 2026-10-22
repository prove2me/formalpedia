-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_constant_fibre_contact_localization_matched_local_bound
-- name    : OAI.PiExponent.FormalInterpolation.constant_fibre_contact_localization_matched_local_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-21T04:01:38.299628+00:00
-- url     : https://prove2.me/theorems/b34f46a1-5964-4b04-839f-b9157cbb5044
-- title:
--   Matched center gives a pointwise contact bound
-- statement:
--   At each place, bound contact with the product ideal by the order of the matched center’s k-coordinate factor, multiplied by its exponent.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Definitions.Def_OAI_PiExponent_LogarithmicInterpolationNumerics
import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Mathlib.RingTheory.Algebraic.Defs

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.constant_fibre_contact_localization_matched_local_bound
    {m K : Nat} (c : Fin K → Fin m → Complex)
    (hc : ∀ i : Fin m, Function.Injective (fun j : Fin K => c j i))
    (T : Fin m → Nat) (e : Fin (m + 1) → Nat)
    (E : Type) [Field E] [Algebra Complex E] [Algebra.EssFiniteType Complex E]
    (htrdeg : Algebra.trdeg Complex E = 1) (x : Fin (m + 1) → E)
    (hgen : IntermediateField.adjoin Complex (Set.range x) = ⊤)
    (hfibre : x 0 = 1)
    (i0 : Fin m) (a : Complex) (ha : x i0.succ = algebraMap Complex E a)
    (k : Fin m) (hk : Transcendental Complex (x k.succ))
    (j : Fin K) (hj : c j i0 = a) (nu : PolynomialCurvePlace E) :
    (polynomialCurveIdealContact nu x (logarithmicCentersIdeal c T e) : Real) ≤
      (e k.succ : Real) *
        max (polynomialCurveOrder nu
          (x k.succ - algebraMap Complex E (c j k)) : Real) 0 := by sorry
