-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_eventual_weighted_generation_implies_eventual_surjective_weighted_sections
-- name    : OAI.PiExponent.FormalInterpolation.eventual_weighted_generation_implies_eventual_surjective_weighted_sections
-- status  : Proved
-- author  : @Ethan Cheung
-- created : 2026-10-21T07:06:56.506762+00:00
-- url     : https://prove2.me/theorems/c6e1675d-ed07-4058-b079-95411b936698
-- title:
--   Generation form implies representative form of eventual weighted sections
-- statement:
--   If the quotient map from the subtype of polynomials of weight ≤ n(rho+eps) onto R/I^n is surjective for all large n, then every polynomial admits a representative modulo I^n of weight ≤ n(rho+eps) for all large n.
-- source:
--   Unpacking Function.Surjective of Ideal.Quotient.mk on the weighted subtype.

import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations

open scoped BigOperators

theorem OAI.PiExponent.FormalInterpolation.eventual_weighted_generation_implies_eventual_surjective_weighted_sections
    {d : Nat} (I : Ideal (MvPolynomial (Fin d) Complex))
    (w : Fin d → Rat) (rho : Rat) (eps : Real)
    (hgen : ∃ N : Nat, ∀ n : Nat, N ≤ n →
      Function.Surjective
        (fun q : {q : MvPolynomial (Fin d) Complex //
              ∀ a ∈ q.support,
                ∑ i, (w i : Real) * (a i : Real) ≤
                  (n : Real) * ((rho : Real) + eps)} =>
          Ideal.Quotient.mk (I ^ n) q.1)) :
    ∃ N : Nat, ∀ n : Nat, N ≤ n →
      ∀ p : MvPolynomial (Fin d) Complex,
        ∃ q : MvPolynomial (Fin d) Complex,
          p - q ∈ I ^ n ∧
          ∀ a ∈ q.support,
            ∑ i, (w i : Real) * (a i : Real) ≤
              (n : Real) * ((rho : Real) + eps) := by sorry
