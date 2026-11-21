-- Prove2me | Theorems.Thm_GRH_nonprincipal_corrected_prime_ramp_abs_le_of_zero_bound
-- name    : GRH.nonprincipal_corrected_prime_ramp_abs_le_of_zero_bound
-- status  : Proved
-- author  : @marozols
-- created : 2026-11-21T04:05:25.295544+00:00
-- url     : https://prove2.me/theorems/5fd56414-b029-4410-9f5a-fdee501f34cd
-- title:
--   Corrected nonprincipal prime-ramp bound at a zero-free boundary
-- statement:
--   Fix a positive modulus $q$ and a nonprincipal Dirichlet character $\chi\bmod q$. Let $3/4\le\beta<1$ and suppose that every zero of $L(s,\chi)$ has real part at most $\beta$. Define
--   $$G_\chi(y)=\sum_{1\le n\le y}\Lambda(n)\operatorname{Re}\chi(n)(y/n-1)_+ + y\operatorname{Re}\frac{L'(1,\chi)}{L(1,\chi)}.$$
--   There is a constant $C\ge0$ such that $|G_\chi(y)|\le C y^\beta$ for every $y>1$. This applies with the exponent equal to the zero-free boundary, including the possibility of zeros on the boundary. It gives the endpoint of the arithmetic window estimate at any certified boundary in the specified range.
-- source:
--   Davenport, Multiplicative Number Theory, §16. Local partial fractions as verified at https://prove2.me/theorems/d5a79704-2d17-4acd-bf91-80ec20436839.

import Mathlib

open Finset ArithmeticFunction Set

namespace GRH

theorem nonprincipal_corrected_prime_ramp_abs_le_of_zero_bound {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (β : ℝ) (hβ₀ : 3/4 ≤ β) (hβ₁ : β < 1)
    (hZero : ∀ z : ℂ, χ.LFunction z = 0 → z.re ≤ β) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : ℝ, 1 < y →
      |(∑ n ∈ range (⌊y⌋₊+1), vonMangoldt n * (χ (n:ZMod q)).re * max (y/(n:ℝ)-1) 0) +
        y * (deriv χ.LFunction 1 / χ.LFunction 1).re| ≤ C*y^β := by sorry

end GRH
