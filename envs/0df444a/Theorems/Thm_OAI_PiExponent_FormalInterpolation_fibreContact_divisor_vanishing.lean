-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_fibreContact_divisor_vanishing
-- name    : OAI.PiExponent.FormalInterpolation.fibreContact_divisor_vanishing
-- status  : Disproved
-- author  : @Eyal1990
-- created : 2026-10-23T08:45:26.338468+00:00
-- url     : https://prove2.me/theorems/4eef8b25-3432-4615-883f-a30cc159d3c9
-- title:
--   Excess contact contradicts the curve divisor bound
-- statement:
--   A nonzero polynomial on a generating one-dimensional function field cannot have local zero orders whose weighted sum exceeds its weighted pole bound. With the stated local contact estimate, the divisor inequality bounds total ideal contact by R/(1+2σ) times total weighted pole degree. The strict excess assumption uses R/(1+σ), which is larger for σ>0, so evaluation must vanish.
-- source:
--   openai/math Approximation FibreNormalRigidity: nonconstant fibre coordinates imply quantitative contact bound.

import Definitions.Def_OAI_PiExponent_FibreContactAuxiliaryData
import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Mathlib.FieldTheory.IsAlgClosed.Basic

open scoped BigOperators
open OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.fibreContact_divisor_vanishing
    {m K : Nat} (E : Type) [Field E] [Algebra Complex E]
    [Algebra.EssFiniteType Complex E]
    (htrdeg : Algebra.trdeg Complex E = 1)
    (x : Fin (m + 1) → E)
    (hgen : IntermediateField.adjoin Complex (Set.range x) = ⊤)
    (hfibre : x 0 = 1)
    (w : Fin (m + 1) → Rat) (R sigma : Rat)
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
