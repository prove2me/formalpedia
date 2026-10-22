-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_constant_fibre_contact_localization
-- name    : OAI.PiExponent.FormalInterpolation.constant_fibre_contact_localization
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-20T23:09:20.34231+00:00
-- url     : https://prove2.me/theorems/812bea0b-3f02-47c6-aabe-47edfe929f12
-- title:
--   Localize constant-fibre contact to one center and one coordinate divisor
-- statement:
--   This child removes the product-ideal and local-contact argument. On x₀=1, each logarithmic positive coordinate evaluates to xᵢ−cⱼᵢ, since every truncated logarithm vanishes at zero. Injectivity at i₀ permits at most one center matching a. If none matches, multiply the constant-coordinate generators from all center ideals; its evaluation is a nonzero constant, proving zero contact everywhere. If j matches, use its k-coordinate generator and the constant-coordinate generators from every other center. Their product belongs to the product ideal and evaluates to a nonzero constant times (xₖ₊₁−cⱼₖ) raised to eₖ₊₁. At affine places its order bounds the defining natural-number infimum; elsewhere contact is zero. The finite support of the nonzero function's zero divisor then justifies summing this pointwise bound. This is a new argument for the supplied definitions, not an imported proof. The remaining obligations are generator evaluation, product-ideal membership, the infimum comparison, and finite-support bookkeeping. K=0 gives the empty product and zero contact. If any exponent is zero, all center ideals are the unit ideal, so the first branch applies.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Definitions.Def_OAI_PiExponent_LogarithmicInterpolationNumerics
import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Mathlib.RingTheory.Algebraic.Defs

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.constant_fibre_contact_localization
    {m K : Nat} (c : Fin K → Fin m → Complex)
    (hc : ∀ i : Fin m, Function.Injective (fun j : Fin K => c j i))
    (T : Fin m → Nat) (e : Fin (m + 1) → Nat)
    (E : Type) [Field E] [Algebra Complex E] [Algebra.EssFiniteType Complex E]
    (htrdeg : Algebra.trdeg Complex E = 1) (x : Fin (m + 1) → E)
    (hgen : IntermediateField.adjoin Complex (Set.range x) = ⊤)
    (hfibre : x 0 = 1)
    (i0 : Fin m) (a : Complex) (ha : x i0.succ = algebraMap Complex E a)
    (k : Fin m) (hk : Transcendental Complex (x k.succ)) :
    (∑ᶠ nu : PolynomialCurvePlace E,
      (polynomialCurveIdealContact nu x (logarithmicCentersIdeal c T e) : Real)) = 0 ∨
    ∃ j : Fin K, c j i0 = a ∧
      (∑ᶠ nu : PolynomialCurvePlace E,
        (polynomialCurveIdealContact nu x (logarithmicCentersIdeal c T e) : Real)) ≤
        (e k.succ : Real) *
          ∑ᶠ nu : PolynomialCurvePlace E,
            max (polynomialCurveOrder nu
              (x k.succ - algebraMap Complex E (c j k)) : Real) 0 := by sorry
