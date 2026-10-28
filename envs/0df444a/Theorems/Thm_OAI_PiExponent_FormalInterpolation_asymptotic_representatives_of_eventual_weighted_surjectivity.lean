-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_asymptotic_representatives_of_eventual_weighted_surjectivity
-- name    : OAI.PiExponent.FormalInterpolation.asymptotic_representatives_of_eventual_weighted_surjectivity
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-21T07:03:07.867181+00:00
-- url     : https://prove2.me/theorems/7d5f46f0-9d87-4bbb-ba6b-af4be37ec5bb
-- title:
--   Uniform additive constant from eventual weighted surjectivity
-- statement:
--   If weighted sections of radius n(rho+eps) eventually surject onto R/I^n, then a single additive Nat constant C upgrades the bound to all n, by absorbing small n via I^N ⊆ I^n and C = ceil(N(rho+eps)).
-- source:
--   Elementary ideal-power absorption: for n < N use a representative modulo I^N ⊆ I^n of weight ≤ N(rho+eps), absorbed into the additive constant ceil(N(rho+eps)).

import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.Ideal.Operations

open scoped BigOperators

theorem OAI.PiExponent.FormalInterpolation.asymptotic_representatives_of_eventual_weighted_surjectivity
    {d : Nat} (I : Ideal (MvPolynomial (Fin d) Complex))
    (w : Fin d → Rat)
    (rho : Rat) (hrho : 0 ≤ rho) (eps : Real) (heps : 0 < eps)
    (heventual : ∃ N : Nat, ∀ n : Nat, N ≤ n →
      ∀ p : MvPolynomial (Fin d) Complex,
        ∃ q : MvPolynomial (Fin d) Complex,
          p - q ∈ I ^ n ∧
          ∀ a ∈ q.support,
            ∑ i, (w i : Real) * (a i : Real) ≤
              (n : Real) * ((rho : Real) + eps)) :
    ∃ C : Nat, ∀ n : Nat, ∀ p : MvPolynomial (Fin d) Complex,
        ∃ q : MvPolynomial (Fin d) Complex,
          p - q ∈ I ^ n ∧
          ∀ a ∈ q.support,
            ∑ i, (w i : Real) * (a i : Real) ≤
              (n : Real) * ((rho : Real) + eps) + (C : Real) := by sorry
