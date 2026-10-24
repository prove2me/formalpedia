-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_quotient_representatives_of_finite_bounded_family
-- name    : OAI.PiExponent.FormalInterpolation.quotient_representatives_of_finite_bounded_family
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T08:38:34.968417+00:00
-- url     : https://prove2.me/theorems/c98bd67a-7fe8-4107-ba9c-6722da03d193
-- title:
--   Finite bounded algebra family gives quotient representatives
-- statement:
--   If a finite family in `I^s` has weighted degree at most `D` and its generated subalgebra makes the polynomial ring a finite module, then sufficiently high ordinary powers admit quotient representatives with the stated asymptotic weighted-degree bound whenever `D/s < rho + eps`.
-- source:
--   openai/math Ampleness stack: WeightedIdealCurveBound implies eps-ample exceptional twist, hence Serre vanishing and eventual generation of I^n by weight ≤ n(rho+eps) sections.

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

open scoped BigOperators
open OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.quotient_representatives_of_finite_bounded_family
    {d : Nat} (I : Ideal (MvPolynomial (Fin d) Complex))
    (w : Fin d → Rat) (rho : Rat) (eps : Real)
    (s : Nat) (hs : 0 < s) (D : Nat)
    (hD : (D : Real) < (s : Real) * ((rho : Real) + eps))
    (m : Nat) (g : Fin m → MvPolynomial (Fin d) Complex)
    (hg : ∀ j, g j ∈ I ^ s)
    (hdeg : ∀ j, ∀ a ∈ (g j).support,
      ∑ k, (w k : Real) * (a k : Real) ≤ (D : Real))
    (hmod : Module.Finite (Algebra.adjoin Complex (Set.range g))
      (MvPolynomial (Fin d) Complex)) :
    ∃ C : Real, 0 ≤ C ∧ ∃ N : Nat, ∀ n : Nat, N ≤ n →
      ∀ q : MvPolynomial (Fin d) Complex, ∃ p : MvPolynomial (Fin d) Complex,
        q - p ∈ I ^ n ∧
        ∀ a ∈ p.support,
          ∑ k, (w k : Real) * (a k : Real) ≤
            (n : Real) * ((rho : Real) + eps) + C := by sorry
