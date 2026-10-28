-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_fibreContact_divisor_vanishing_of_posWeights
-- name    : OAI.PiExponent.FormalInterpolation.fibreContact_divisor_vanishing_of_posWeights
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-24T04:11:15.371956+00:00
-- url     : https://prove2.me/theorems/8dc819a8-9628-46f3-811d-5ed60bf37543
-- title:
--   Positive weighted poles bound excess fibre contact
-- statement:
--   For a polynomial with weighted support at most N and strictly positive coordinate weights, local order bounds force vanishing if total ideal contact strictly exceeds the stated weighted pole allowance. The independent proof route bounds the evaluated polynomial's pole divisor from its support, then uses the principal-divisor degree relation and the strict gap between 1+σ and 1+2σ. Positive weights are essential to this corrected form; the disproved predecessor allowed zero weights.
-- source:
--   openai/math Approximation FibreNormalRigidity: nonconstant fibre coordinates imply quantitative contact bound.

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Definitions.Def_OAI_PiExponent_FibreContactAuxiliaryData
import Mathlib.FieldTheory.IsAlgClosed.Basic

open scoped BigOperators
open OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.fibreContact_divisor_vanishing_of_posWeights
    {m : Nat} (E : Type) [Field E] [Algebra Complex E]
    [Algebra.EssFiniteType Complex E]
    (htrdeg : Algebra.trdeg Complex E = 1)
    (x : Fin (m + 1) → E)
    (hgen : IntermediateField.adjoin Complex (Set.range x) = ⊤)
    (w : Fin (m + 1) → Rat)
    (hw : ∀ i, 0 < (w i : Real))
    (R sigma : Rat)
    (hR : 0 < R) (hsigma : 0 < (sigma : Real))
    (N : Nat) (hN : 0 < N)
    (P : MvPolynomial (Fin m) Complex)
    (hP : fibreContactSupportBound (fun i => w i.succ) N P)
    (I : Ideal (MvPolynomial (Fin (m + 1)) Complex))
    (hexcess :
      (R : Real) / (1 + (sigma : Real)) *
        (∑ᶠ nu : PolynomialCurvePlace E, polynomialCurvePole nu x w) <
      (∑ᶠ nu : PolynomialCurvePlace E,
        (polynomialCurveIdealContact nu x I : Real)))
    (hlocal : MvPolynomial.aeval (fun i => x i.succ) P ≠ 0 →
      ∀ nu : PolynomialCurvePlace E,
        ((polynomialCurveIdealContact nu x I : Real) *
          ((1 + 2 * (sigma : Real)) * (N : Real))) ≤
          (R : Real) * max 0
            (polynomialCurveOrder nu
              (MvPolynomial.aeval (fun i => x i.succ) P) : Real)) :
    MvPolynomial.aeval (fun i => x i.succ) P = 0 := by sorry
