-- Prove2me | Theorems.Thm_NymanBeurling_nonnegative_coefficients_cost_ge_one_div_42
-- name    : NymanBeurling.nonnegative_coefficients_cost_ge_one_div_42
-- status  : Proved
-- author  : @Yi
-- created : 2026-11-21T00:53:06.484863+00:00
-- url     : https://prove2.me/theorems/e239a71c-da02-42f5-bee3-bb9ee7b93934
-- title:
--   Nonnegative Nyman–Beurling coefficients force remainder cost at least $1/42$
-- statement:
--   Let $c$ be a finitely supported rational sequence with $c_k\ge0$ for every $k$, and write
--   $$e_c(m)=1-\sum_{d\ge2} c_{d-2}\frac{m\bmod d}{d}.$$
--   For every integer $H\ge0$, its Nyman–Beurling certificate cost satisfies
--   $$\sum_{m=1}^H\frac{e_c(m)^2}{m(m+1)}+\frac{(1+\sum_k|c_k|)^2}{H+1}\ \ge\ \frac1{42}.$$
--   Consequently every certificate with cost strictly below $1/42$ must contain a negative coefficient. A finite signed certificate is already known with cost below $1/43$.
-- source:
--   Finite dual certificate for NymanBeurling.arbitrarily_small_remainder_certificates, https://prove2.me/theorems/5b7b7b22-9280-4b04-9e90-f2f88cb85339 . The signed comparison witness is NymanBeurling.finite_remainder_certificates_through_42, https://prove2.me/theorems/ed644939-4ab2-4240-9464-c2c11589f785 . Integer dual weights were chosen using a finite nonnegative least-squares calculation and checked by exact arithmetic.

import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

set_option autoImplicit false

theorem NymanBeurling.nonnegative_coefficients_cost_ge_one_div_42 (c : ℕ →₀ ℚ) (hc : ∀ k, 0 ≤ c k) (H : ℕ) :
    (1/42 : ℚ) ≤ (∑ n ∈ Finset.range H, (1 - ∑ k ∈ c.support, c k *
          (((n+1) % (k+2) : ℕ) : ℚ) / ((k+2 : ℕ) : ℚ))^2 /
          ((n+1 : ℚ)*(n+2 : ℚ))) +
      (1 + ∑ k ∈ c.support, |c k|)^2/(H+1) := by sorry
