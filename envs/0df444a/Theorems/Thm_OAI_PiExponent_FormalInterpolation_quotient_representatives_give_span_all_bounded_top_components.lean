-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_quotient_representatives_give_span_all_bounded_top_components
-- name    : OAI.PiExponent.FormalInterpolation.quotient_representatives_give_span_all_bounded_top_components
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T08:35:18.283148+00:00
-- url     : https://prove2.me/theorems/4304e382-83ff-4f2a-a280-4f8abc9e7706
-- title:
--   Subcritical representatives yield coordinate powers in the top-component span
-- statement:
--   Use the representative bound with a rate strictly below R to choose one common weighted degree D between the representative cutoff and sR. Subtract a low-weight representative from a coordinate monomial of degree D; its top component is that monomial, giving the required coordinate powers in the span.
-- source:
--   openai/math Ampleness stack: WeightedIdealCurveBound implies eps-ample exceptional twist, hence Serre vanishing and eventual generation of I^n by weight ≤ n(rho+eps) sections.

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

open scoped BigOperators
open OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.quotient_representatives_give_span_all_bounded_top_components
    {d : Nat} (I : Ideal (MvPolynomial (Fin d) Complex))
    (w : Fin d → Rat) (hw : ∀ i, 0 < (w i : Real))
    (rho : Rat) (hrho : 0 ≤ rho)
    (R : Real) (hR : (rho : Real) < R)
    (eps : Real) (heps : 0 < eps)
    (C : Real) (hC : 0 ≤ C) (N : Nat)
    (hrate : (rho : Real) + eps < R)
    (hrepr : ∀ n : Nat, N ≤ n →
      ∀ q : MvPolynomial (Fin d) Complex, ∃ p : MvPolynomial (Fin d) Complex,
        q - p ∈ I ^ n ∧
        ∀ a ∈ p.support,
          ∑ k, (w k : Real) * (a k : Real) ≤
            (n : Real) * ((rho : Real) + eps) + C) :
    ∃ s : Nat, 0 < s ∧
      ∃ D : Real, 0 < D ∧ D < (s : Real) * R ∧
        ∀ i : Fin d, ∃ e : Nat, 0 < e ∧
          MvPolynomial.X i ^ e ∈
            Ideal.span (Set.range (fun f :
              {p : MvPolynomial (Fin d) Complex //
                p ∈ I ^ s ∧
                ∀ a ∈ p.support,
                  ∑ k, (w k : Real) * (a k : Real) ≤ D} =>
              MvPolynomial.weightedHomogeneousComponent
                (fun k => (w k : Real)) D f.1)) := by sorry
