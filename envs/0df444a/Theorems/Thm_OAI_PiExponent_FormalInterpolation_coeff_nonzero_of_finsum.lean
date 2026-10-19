-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_coeff_nonzero_of_finsum
-- name    : OAI.PiExponent.FormalInterpolation.coeff_nonzero_of_finsum
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-18T12:46:38.464316+00:00
-- url     : https://prove2.me/theorems/0958d845-c1e7-41e1-b315-2587d8d3b93a
-- title:
--   Nonzero coefficient in a finite polynomial sum
-- statement:
--   If a polynomial is a finite sum and its coefficient at a monomial is nonzero, then at least one summand has a nonzero coefficient at that monomial.

import Mathlib.RingTheory.MvPolynomial.Ideal

open scoped BigOperators

theorem OAI.PiExponent.FormalInterpolation.coeff_nonzero_of_finsum
    {σ : Type*} [Fintype σ] {k : Type*} [CommSemiring k]
    (m : Nat) (f : Fin m → MvPolynomial σ k) (p : MvPolynomial σ k)
    (d : σ →₀ Nat) (hp : p = ∑ j, f j) (hd : p.coeff d ≠ 0) :
    ∃ j, (f j).coeff d ≠ 0 := by sorry
