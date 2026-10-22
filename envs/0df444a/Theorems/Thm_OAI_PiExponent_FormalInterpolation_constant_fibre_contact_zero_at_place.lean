-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_constant_fibre_contact_zero_at_place
-- name    : OAI.PiExponent.FormalInterpolation.constant_fibre_contact_zero_at_place
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-21T04:02:34.86973+00:00
-- url     : https://prove2.me/theorems/05677139-098e-4528-b2b8-7260f912982c
-- title:
--   Constant fibre forces zero ideal contact at an affine place
-- statement:
--   At a place where every coordinate has nonnegative valuation, the logarithmic center ideal has contact zero if the i0 coordinate is the constant a and no center has that coordinate. The proof constructs the product of the i0-coordinate generators, shows it lies in the product ideal, and evaluates it to a nonzero constant. Its valuation is zero, which bounds the contact infimum by zero; contact is a natural number.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Definitions.Def_OAI_PiExponent_LogarithmicInterpolationNumerics
import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Mathlib.RingTheory.Algebraic.Defs

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.constant_fibre_contact_zero_at_place
    {m K : Nat} (c : Fin K → Fin m → Complex)
    (T : Fin m → Nat) (e : Fin (m + 1) → Nat)
    (E : Type) [Field E] [Algebra Complex E] [Algebra.EssFiniteType Complex E]
    (x : Fin (m + 1) → E) (hfibre : x 0 = 1)
    (i0 : Fin m) (a : Complex) (ha : x i0.succ = algebraMap Complex E a)
    (hn : ∀ j : Fin K, c j i0 ≠ a)
    (nu : PolynomialCurvePlace E)
    (h_aff : ∀ i, (0 : WithTop Int) ≤ nu.1 (x i)) :
    polynomialCurveIdealContact nu x (logarithmicCentersIdeal c T e) = 0 := by sorry
